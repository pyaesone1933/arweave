%%% @doc The server responsible for processing blocks and transactions and
%%% maintaining the node state. Blocks are prioritized over transactions.
%%% The state is synchronized with the ar_node process for non-blocking reads.
-module(ar_node_worker).

-export([start_link/1]).

-export([init/1, handle_cast/2, terminate/2]).

-include("ar.hrl").
-include("ar_data_sync.hrl").
-include_lib("eunit/include/eunit.hrl").

-ifdef(DEBUG).
-define(PROCESS_TASK_QUEUE_FREQUENCY_MS, 10).
-else.
-define(PROCESS_TASK_QUEUE_FREQUENCY_MS, 200).
-endif.

%%%===================================================================
%%% Public interface.
%%%===================================================================

start_link(Args) ->
	gen_server:start_link({local, ?MODULE}, ?MODULE, Args, []).

%%%===================================================================
%%% Generic server callbacks.
%%%===================================================================

init(State) ->
	%% The message queue of this process may grow big under load.
	%% The flag makes VM store messages off heap and do not perform
	%% expensive GC on them.
	process_flag(message_queue_data, off_heap),
	process_flag(trap_exit, true),
	gen_server:cast(self(), process_task_queue),
	{ok, State#{ task_queue => gb_sets:new() }}.

handle_cast(process_task_queue, #{ task_queue := TaskQueue } = State) ->
	case gb_sets:is_empty(TaskQueue) of
		true ->
			timer:apply_after(
				?PROCESS_TASK_QUEUE_FREQUENCY_MS,
				gen_server,
				cast,
				[self(), process_task_queue]
			),
			{noreply, State};
		false ->
			record_metrics(State),
			{{_Priority, Task}, TaskQueue2} = gb_sets:take_smallest(TaskQueue),
			gen_server:cast(self(), process_task_queue),
			handle_task(Task, State#{ task_queue => TaskQueue2 })
	end;

handle_cast(Message, #{ task_queue := TaskQueue } = State) ->
	Task = {priority(Message), Message},
	case gb_sets:is_element(Task, TaskQueue) of
		true ->
			{noreply, State};
		false ->
			{noreply, State#{ task_queue => gb_sets:insert(Task, TaskQueue) }}
	end.

terminate(Reason, #{ miner := Miner }) ->
	case Miner of
		undefined -> do_nothing;
		PID -> ar_mine:stop(PID)
	end,
	ar:info([
		{event, ar_node_worker_terminated},
		{reason, Reason}
	]).

%%%===================================================================
%%% Private functions.
%%%===================================================================

record_metrics(State) ->
	#{
		height := Height,
		mempool_size := MempoolSize,
		weave_size := WeaveSize
	} = State,
	prometheus_gauge:set(arweave_block_height, Height),
	record_mempool_size_metrics(MempoolSize),
	prometheus_gauge:set(weave_size, WeaveSize).

record_mempool_size_metrics({HeaderSize, DataSize}) ->
	prometheus_gauge:set(mempool_header_size_bytes, HeaderSize),
	prometheus_gauge:set(mempool_data_size_bytes, DataSize).

handle_task({gossip_message, Msg}, #{ gossip := GS } = State) ->
	{GS2, Message} = ar_gossip:recv(GS, Msg),
	handle_gossip({GS2, Message}, State#{ gossip => GS2 });

handle_task({add_tx, TX}, State) ->
	handle_add_tx(State, TX, maps:get(gossip, State));

handle_task({move_tx_to_mining_pool, TX}, State) ->
	handle_move_tx_to_mining_pool(State, TX, maps:get(gossip, State));

handle_task({process_new_block, Peer, Height, BShadow, BDS, ReceiveTimestamp}, State) ->
	%% We have a new block. Distribute it to the gossip network. This is only
	%% triggered in the polling mode.
	GS = maps:get(gossip, State),
	ar_gossip:send(GS, {new_block, Peer, Height, BShadow, BDS, ReceiveTimestamp}),
	{noreply, State};

handle_task({work_complete, BaseBH, NewB, MinedTXs, BDS, POA}, State) ->
	#{ block_index := [{CurrentBH, _, _} | _]} = State,
	case BaseBH of
		CurrentBH ->
			handle_block_from_miner(State, NewB, MinedTXs, BDS, POA);
		_ ->
			ar:info([{event, ignore_mined_block}, {reason, accepted_foreign_block}]),
			{noreply, State}
	end;

handle_task({fork_recovered, BI, BlockTXPairs, BaseH}, State) ->
	handle_recovered_from_fork(State, BI, BlockTXPairs, BaseH);

handle_task(mine, State) ->
	{noreply, ar_node_utils:start_mining(State)};

handle_task(automine, State) ->
	{noreply, ar_node_utils:start_mining(State#{ automine => true })};

handle_task({set_reward_addr, Addr}, #{ node := Node } = State) ->
	Node ! {sync_reward_addr, Addr},
	{noreply, State#{ reward_addr => Addr }};

handle_task({set_trusted_peers, Peers}, #{ node := Node } = State) ->
	Node ! {sync_trusted_peers, Peers},
	{noreply, State#{ trusted_peers => Peers }};

handle_task({add_peers, Peers}, #{ gossip := GS } = State) ->
	NewGS = ar_gossip:add_peers(GS, Peers),
	{noreply, State#{ gossip => NewGS }};

handle_task({set_loss_probability, Prob}, #{ gossip := GS } = State) ->
	{noreply, State#{ gossip => ar_gossip:set_loss_probability(GS, Prob) }};

handle_task(Msg, State) ->
	ar:err([
		{event, ar_node_worker_received_unknown_message},
		{message, Msg}
	]),
	{noreply, State}.

%% @doc Handle the gossip receive results.
handle_gossip({_NewGS, {new_block, Peer, _Height, BShadow, _BDS, ReceiveTimestamp}}, State) ->
	handle_new_block(State, BShadow, Peer, ReceiveTimestamp);

handle_gossip({NewGS, {add_tx, TX}}, State) ->
	handle_add_tx(State, TX, NewGS);

handle_gossip({NewGS, {add_waiting_tx, TX}}, State) ->
	handle_add_waiting_tx(State, TX, NewGS);

handle_gossip({NewGS, {move_tx_to_mining_pool, TX}}, State) ->
	handle_move_tx_to_mining_pool(State, TX, NewGS);

handle_gossip({NewGS, {drop_waiting_txs, TXs}}, State) ->
	handle_drop_waiting_txs(State, TXs, NewGS);

handle_gossip({_NewGS, ignore}, State) ->
	{noreply, State};

handle_gossip({_NewGS, UnknownMessage}, State) ->
	ar:info([
		{event, ar_node_worker_received_unknown_gossip_message},
		{message, UnknownMessage}
	]),
	{noreply, State}.

%% @doc Add the new transaction to the server state.
handle_add_tx(State, TX, GS) ->
	#{ node := Node, txs := TXs, mempool_size := MS} = State,
	{NewGS, _} = ar_gossip:send(GS, {add_tx, TX}),
	IncreasedMempoolSize = ar_node_utils:increase_mempool_size(MS, TX),
	Node ! {sync_mempool_tx, TX#tx.id, {TX, ready_for_mining}, IncreasedMempoolSize},
	{noreply, State#{
		txs => maps:put(TX#tx.id, {TX, ready_for_mining}, TXs),
		gossip => NewGS,
		mempool_size => IncreasedMempoolSize
	}}.

%% @doc Add the new waiting transaction to the server state.
handle_add_waiting_tx(State, TX, GS) ->
	#{ node := Node, txs := WaitingTXs, mempool_size := MS } = State,
	{NewGS, _} = ar_gossip:send(GS, {add_waiting_tx, TX}),
	IncreasedMempoolSize = ar_node_utils:increase_mempool_size(MS, TX),
	Node ! {sync_mempool_tx, TX#tx.id, {TX, waiting}, IncreasedMempoolSize},
	{noreply, State#{
		txs => maps:put(TX#tx.id, {TX, waiting}, WaitingTXs),
		gossip => NewGS,
		mempool_size => IncreasedMempoolSize
	}}.

%% @doc Add the transaction to the mining pool, to be included in the mined block.
handle_move_tx_to_mining_pool(State, TX, GS) ->
	#{ node := Node, txs := TXs } = State,
	{NewGS, _} = ar_gossip:send(GS, {move_tx_to_mining_pool, TX}),
	Node ! {sync_mempool_tx, TX#tx.id, {TX, ready_for_mining}},
	{noreply, State#{
		txs => maps:put(TX#tx.id, {TX, ready_for_mining}, TXs),
		gossip => NewGS
	}}.

handle_drop_waiting_txs(State, DroppedTXs, GS) ->
	#{ node := Node, txs := TXs, mempool_size := {MempoolHeaderSize, MempoolDataSize} } = State,
	{NewGS, _} = ar_gossip:send(GS, {drop_waiting_txs, DroppedTXs}),
	{UpdatedTXs, DroppedTXMap} = lists:foldl(
		fun(TX, {Acc, DroppedAcc}) ->
			case maps:take(TX#tx.id, Acc) of
				{Value, Map} ->
					{Map, maps:put(TX#tx.id, Value, DroppedAcc)};
				error ->
					{Acc, DroppedAcc}
			end
		end,
		{TXs, maps:new()},
		DroppedTXs
	),
	{DroppedHeaderSize, DroppedDataSize} = ar_node_utils:calculate_mempool_size(DroppedTXMap),
	DecreasedMempoolSize =
		{MempoolHeaderSize - DroppedHeaderSize, MempoolDataSize - DroppedDataSize},
	Node ! {sync_dropped_mempool_txs, DroppedTXMap, DecreasedMempoolSize},
	{noreply, State#{
		txs => UpdatedTXs,
		gossip => NewGS,
		mempool_size => DecreasedMempoolSize
	}}.

%% @doc Validate whether a new block is legitimate, then handle it, optionally
%% dropping or starting a fork recovery as appropriate.
handle_new_block(#{ block_index := not_joined } = State, BShadow, _Peer, _ReceiveTimestamp) ->
	ar:info([
		{event, ar_node_worker_ignored_block},
		{reason, not_joined},
		{indep_hash, ar_util:encode(BShadow#block.indep_hash)}
	]),
	{noreply, State};
handle_new_block(#{ height := Height } = State, BShadow, _Peer, _ReceiveTimestamp)
		when BShadow#block.height =< Height ->
	ar:info([
		{event, ar_node_worker_ignored_block},
		{reason, height_lower_than_current},
		{indep_hash, ar_util:encode(BShadow#block.indep_hash)}
	]),
	{noreply, State};
handle_new_block(#{ height := Height } = State, BShadow, Peer, ReceiveTimestamp)
		when BShadow#block.height >= Height + 1 ->
	ShadowHeight = BShadow#block.height,
	ShadowHL = BShadow#block.hash_list,
	#{ block_index := BI,  block_txs_pairs := BlockTXPairs } = State,
	case get_diverged_block_hashes(ShadowHeight, ShadowHL, BI) of
		{error, no_intersection} ->
			ar:warn([
				{event, new_block_shadow_block_index_no_intersection},
				{block_shadow_hash_list,
					lists:map(
						fun ar_util:encode/1,
						lists:sublist(ShadowHL, ?STORE_BLOCKS_BEHIND_CURRENT)
					)},
				{node_hash_list_last_blocks,
					lists:map(
						fun({H, _, _}) -> ar_util:encode(H) end,
						lists:sublist(BI, ?STORE_BLOCKS_BEHIND_CURRENT)
					)}
			]),
			{noreply, State};
		{ok, {}} ->
			apply_new_block(
				State,
				BShadow#block{ hash_list = ?BI_TO_BHL(BI) },
				Peer,
				ReceiveTimestamp
			);
		{ok, {DivergedHashes, BIBase}} ->
			HeightBase = length(BIBase) - 1,
			{_, BlockTXPairsBase} = lists:split(Height - HeightBase, BlockTXPairs),
			RecoveryHashes = [BShadow#block.indep_hash | DivergedHashes],
			maybe_fork_recover(State, BShadow, Peer, RecoveryHashes, BIBase, BlockTXPairsBase)
	end.

%% Take a block shadow and the hashes of the recent blocks and return
%% {ok, {a list of diverged hashes, the base block index}} - in this case
%% the block becomes a fork recovery target. If the shadow index matches
%% the head of the current state, return {ok, {}} - this block can be then
%% validated against the current state.
%%
%% Return {error, no_intersection} when there is no common block hash within
%% the last ?STORE_BLOCKS_BEHIND_CURRENT hashes.
get_diverged_block_hashes(ShadowHeight, ShadowHL, BI) ->
	ShortShadowHL = lists:sublist(ShadowHL, ?STORE_BLOCKS_BEHIND_CURRENT),
	ShortHL = ?BI_TO_BHL(lists:sublist(BI, ?STORE_BLOCKS_BEHIND_CURRENT)),
	case get_diverged_block_hashes(ShortShadowHL, ShortHL) of
		{error, no_intersection} = Error ->
			Error;
		{ok, []} ->
			{ok, {}};
		{ok, DivergedHashes} ->
			ForkDepth = length(DivergedHashes),
			Height = length(BI) - 1,
			{_, BIBase} = lists:split(ForkDepth - (ShadowHeight - Height) + 1, BI),
			{ok, {DivergedHashes, BIBase}}
	end.

get_diverged_block_hashes(ShadowHL, HL) ->
	LastShadowH = lists:last(ShadowHL),
	case lists:member(LastShadowH, HL) of
		true ->
			get_diverged_block_hashes_reversed(
				lists:reverse(ShadowHL),
				lists:dropwhile(fun(H) -> H /= LastShadowH end, lists:reverse(HL))
			);
		false ->
			{error, no_intersection}
	end.

get_diverged_block_hashes_reversed([H | Tail1], [H | Tail2]) ->
	get_diverged_block_hashes_reversed(Tail1, Tail2);
get_diverged_block_hashes_reversed([], []) -> {ok, []};
get_diverged_block_hashes_reversed(DivergedHashes, _) ->
	{ok, lists:reverse(DivergedHashes)}.

apply_new_block(State, #block{ txs = TXs }, Peer, _TS) when length(TXs) > ?BLOCK_TX_COUNT_LIMIT ->
	ar:err([
		{event, received_invalid_block},
		{validation_error, tx_count_exceeds_limit},
		{peer, ar_util:format_peer(Peer)}
	]),
	{noreply, State};
apply_new_block(State, BShadow, Peer, ReceiveTimestamp) ->
	#{
		txs := MempoolTXs,
		node := Node,
		block_index := BI,
		block_txs_pairs := BlockTXPairs
	} = State,
	{TXs, MissingTXIDs} = pick_txs(BShadow#block.txs, MempoolTXs),
	case MissingTXIDs of
		[] ->
			case generate_block_from_shadow(State, BShadow, TXs) of
				error ->
					{noreply, State};
				{ok, NewB} ->
					apply_new_block(State, NewB, ReceiveTimestamp)
			end;
		_ ->
			fork_recover(State, Node, Peer, [BShadow#block.indep_hash], BI, BlockTXPairs)
	end.

apply_new_block(State, NewB, ReceiveTimestamp) ->
	#{
		node := Node,
		block_txs_pairs := BlockTXPairs,
		block_index := BI
	} = State,
	B = ar_util:get_head_block(BI),
	TXs = NewB#block.txs,
	Wallets = ar_wallets:get(
		B#block.wallet_list,
		[NewB#block.reward_addr | ar_tx:get_addresses(NewB#block.txs)]
	),
	case ar_node_utils:validate(BI, NewB, B, Wallets, BlockTXPairs) of
		{invalid, Reason} ->
			ar:err([
				{event, received_invalid_block},
				{validation_error, Reason}
			]),
			{noreply, State};
		valid ->
			NewState = ar_node_utils:integrate_new_block(State, NewB, TXs),
			ProcessingTime = timer:now_diff(erlang:timestamp(), ReceiveTimestamp) / 1000000,
			prometheus_histogram:observe(block_processing_time, ProcessingTime),
			Node ! {sync_state, NewState},
			{noreply, NewState}
	end.

generate_block_from_shadow(State, BShadow, TXs) ->
	#{
		reward_pool := RewardPool,
		wallet_list := WalletList,
		height := Height
	} = State,
	B = BShadow#block{ txs = TXs },
	case ar_wallets:apply_block(B, WalletList, RewardPool, Height) of
		{error, invalid_reward_pool} ->
			ar:err([
				{event, received_invalid_block},
				{validation_error, invalid_reward_pool}
			]),
			error;
		{error, invalid_wallet_list} ->
			ar:err([
				{event, received_invalid_block},
				{validation_error, invalid_wallet_list}
			]),
			error;
		ok ->
			{ok, B}
	end.

pick_txs(TXIDs, TXs) ->
	lists:foldr(
		fun(TXID, {Found, Missing}) ->
			case maps:get(TXID, TXs, tx_not_in_mempool) of
				tx_not_in_mempool ->
					%% This disk read should almost never be useful. Presumably,
					%% the only reason to find some of these transactions on disk
					%% is they had been written prior to the call, what means they are
					%% from an orphaned fork, more than one block behind.
					case ar_storage:read_tx(TXID) of
						unavailable ->
							{Found, [TXID | Missing]};
						TX ->
							{[TX | Found], Missing}
					end;
				{TX, _} ->
					{[TX | Found], Missing}
			end
		end,
		{[], []},
		TXIDs
	).

maybe_fork_recover(State, BShadow, Peer, RecoveryHashes, BI, BlockTXPairs) ->
	#{
		block_index := StateBI,
		cumulative_diff := CDiff,
		node:= Node
	} = State,
	case is_fork_preferable(BShadow, CDiff, StateBI) of
		false ->
			{noreply, State};
		true ->
			fork_recover(State, Node, Peer, RecoveryHashes, BI, BlockTXPairs)
	end.

fork_recover(State, Node, Peer, RecoveryHashes, BI, BlockTXPairs) ->
	case {whereis(fork_recovery_server), whereis(join_server)} of
		{undefined, undefined} ->
			PrioritisedPeers = ar_util:unique(Peer) ++
				case whereis(http_bridge_node) of
					undefined -> [];
					BridgePID -> ar_bridge:get_remote_peers(BridgePID)
				end,
			PID = ar_fork_recovery:start(
				PrioritisedPeers,
				RecoveryHashes,
				BI,
				Node,
				BlockTXPairs
			),
			case PID of
				undefined -> ok;
				_ -> erlang:register(fork_recovery_server, PID)
			end;
		{undefined, _} ->
			ok;
		_ ->
			whereis(fork_recovery_server) ! {update_target_hashes, RecoveryHashes, Peer}
	end,
	{noreply, State}.

%% @doc Integrate the block found by us.
handle_block_from_miner(#{ block_index := not_joined } = State, _NewB, _TXs, _BDS, _POA) ->
	{noreply, State};
handle_block_from_miner(StateIn, NewB, MinedTXs, BDS, _POA) ->
	#{
		node             := Node,
		block_index      := BI,
		txs              := TXs,
		gossip           := GS,
		block_txs_pairs  := BlockTXPairs,
		weave_size       := WeaveSize,
		wallet_list      := WalletList
	} = StateIn,
	NewBI = ar_node_utils:update_block_index(NewB#block{ txs = MinedTXs }, BI),
	SizeTaggedTXs = ar_block:generate_size_tagged_list_from_txs(MinedTXs),
	ar_data_sync:add_block(SizeTaggedTXs, lists:sublist(NewBI, ?TRACK_CONFIRMATIONS), WeaveSize),
	ar_storage:write_full_block(NewB, MinedTXs),
	BH = NewB#block.indep_hash,
	NewBlockTXPairs = ar_node_utils:update_block_txs_pairs(BH, SizeTaggedTXs, BlockTXPairs),
	{ValidTXs, InvalidTXs} =
		ar_tx_replay_pool:pick_txs_to_keep_in_mempool(
			NewBlockTXPairs,
			lists:foldl(
				fun(TX, Acc) ->
					maps:remove(TX#tx.id, Acc)
				end,
				TXs,
				MinedTXs
			),
			NewB#block.diff,
			NewB#block.height,
			ar_wallets:get(
				NewB#block.wallet_list,
				ar_tx:get_addresses([TX || {TX, _} <- maps:values(TXs)])
			)
		),
	ar_node_utils:drop_invalid_txs(InvalidTXs),
	ar_miner_log:mined_block(NewB#block.indep_hash, NewB#block.height),
	ar:info(
		[
			{event, mined_block},
			{indep_hash, ar_util:encode(NewB#block.indep_hash)},
			{txs, length(MinedTXs)}
		]
	),
	{NewGS, _} = ar_gossip:send(
		GS,
		{new_block, self(), NewB#block.height, NewB, BDS, erlang:timestamp()}
	),
	lists:foreach(
		fun(TX) ->
			ar_downloader:enqueue_random({tx_data, TX}),
			ar_tx_queue:drop_tx(TX)
		end,
		MinedTXs
	),
	BH = element(1, hd(NewBI)),
	RewardAddr = NewB#block.reward_addr,
	ar_wallets:set_current(WalletList, NewB#block.wallet_list, RewardAddr, NewB#block.height),
	NewState = ar_node_utils:reset_miner(
		StateIn#{
			block_index          => NewBI,
			current              => BH,
			gossip               => NewGS,
			txs                  => ValidTXs,
			height               => NewB#block.height,
			reward_pool          => NewB#block.reward_pool,
			diff                 => NewB#block.diff,
			last_retarget        => NewB#block.last_retarget,
			weave_size           => NewB#block.weave_size,
			block_txs_pairs      => NewBlockTXPairs,
			wallet_list          => NewB#block.wallet_list,
			mempool_size         => ar_node_utils:calculate_mempool_size(ValidTXs)
		}
	),
	Node ! {sync_state, NewState},
	{noreply, NewState}.

%% @doc Handle executed fork recovery.
handle_recovered_from_fork(#{ block_index := not_joined } = StateIn, BI, BlockTXPairs, _BaseH) ->
	#{ node := Node, txs := TXs } = StateIn,
	NewB = ar_storage:read_block(element(1, hd(BI))),
	{_, SizeTaggedTXs} = hd(BlockTXPairs),
	ar:info(
		[
			{event, node_joined_successfully},
			{height, NewB#block.height}
		]
	),
	case whereis(fork_recovery_server) of
		undefined -> ok;
		_ -> erlang:unregister(fork_recovery_server)
	end,
	{ValidTXs, InvalidTXs} = ar_tx_replay_pool:pick_txs_to_keep_in_mempool(
		BlockTXPairs,
		TXs,
		NewB#block.diff,
		NewB#block.height,
		ar_wallets:get(
			NewB#block.wallet_list,
			ar_tx:get_addresses([TX || {TX, _} <- maps:values(TXs)])
		)
	),
	ar_node_utils:drop_invalid_txs(InvalidTXs),
	ar_data_sync:add_block(
		SizeTaggedTXs,
		lists:sublist(BI, ?TRACK_CONFIRMATIONS),
		NewB#block.weave_size - NewB#block.block_size
	),
	NewState = ar_node_utils:reset_miner(
		StateIn#{
			block_index          => BI,
			current              => element(1, hd(BI)),
			wallet_list          => NewB#block.wallet_list,
			height               => NewB#block.height,
			reward_pool          => NewB#block.reward_pool,
			txs                  => ValidTXs,
			diff                 => NewB#block.diff,
			last_retarget        => NewB#block.last_retarget,
			weave_size           => NewB#block.weave_size,
			block_txs_pairs      => BlockTXPairs,
			mempool_size         => ar_node_utils:calculate_mempool_size(ValidTXs)
		}
	),
	Node ! {sync_state, NewState},
	{noreply, NewState};
handle_recovered_from_fork(#{ block_index := CurrentBI } = StateIn, BI, BlockTXPairs, BaseH) ->
	case whereis(fork_recovery_server) of
		undefined -> ok;
		_ -> erlang:unregister(fork_recovery_server)
	end,
	NewB = ar_storage:read_block(element(1, hd(BI))),
	case is_fork_preferable(NewB, maps:get(cumulative_diff, StateIn), CurrentBI) of
		true ->
			do_recovered_from_fork(StateIn, NewB, BI, BlockTXPairs, BaseH);
		false ->
			{noreply, StateIn}
	end.

do_recovered_from_fork(StateIn, NewB, BI, BlockTXPairs, BaseH) ->
	#{ node := Node, txs := TXs } = StateIn,
	ar:info(
		[
			{event, fork_recovered_successfully},
			{height, NewB#block.height}
		]
	),
	ar_miner_log:fork_recovered(NewB#block.indep_hash),
	case fork_depth(BaseH, BI) of
		1 ->
			%% The recovery process was initiated to fetch missing transactions. It is not a fork.
			do_not_record_fork_depth_metric;
		Depth ->
			prometheus_histogram:observe(fork_recovery_depth, Depth)
	end,
	{ValidTXs, InvalidTXs} = ar_tx_replay_pool:pick_txs_to_keep_in_mempool(
		BlockTXPairs,
		TXs,
		NewB#block.diff,
		NewB#block.height,
		ar_wallets:get(
			NewB#block.wallet_list,
			ar_tx:get_addresses([TX || {TX, _} <- maps:values(TXs)])
		)
	),
	ar_node_utils:drop_invalid_txs(InvalidTXs),
	AppliedBlockTXPairs = lists:takewhile(fun({BH, _}) -> BH /= BaseH end, BlockTXPairs),
	lists:foreach(
		fun({BH, SizeTaggedTXs}) ->
			BaseBI = lists:sublist(
				lists:dropwhile(fun({H, _, _}) -> BH /= H end, BI),
				?TRACK_CONFIRMATIONS
			),
			[_, {_, StartOffset, _} | _] = BaseBI,
			ar_data_sync:add_block(
				SizeTaggedTXs,
				BaseBI,
				StartOffset
			)
		end,
		lists:reverse(AppliedBlockTXPairs)
	),
	WalletList = (ar_storage:read_block(NewB#block.previous_block))#block.wallet_list,
	RewardAddr = NewB#block.reward_addr,
	ar_wallets:set_current(WalletList, NewB#block.wallet_list, RewardAddr, NewB#block.height),
	NewState = ar_node_utils:reset_miner(
		StateIn#{
			block_index          => BI,
			current              => element(1, hd(BI)),
			wallet_list          => NewB#block.wallet_list,
			height               => NewB#block.height,
			reward_pool          => NewB#block.reward_pool,
			txs                  => ValidTXs,
			diff                 => NewB#block.diff,
			last_retarget        => NewB#block.last_retarget,
			weave_size           => NewB#block.weave_size,
			cumulative_diff      => NewB#block.cumulative_diff,
			block_txs_pairs      => BlockTXPairs,
			mempool_size         => ar_node_utils:calculate_mempool_size(ValidTXs)
		}
	),
	Node ! {sync_state, NewState},
	{noreply, NewState}.

fork_depth(H, BI) ->
	fork_depth(H, BI, 1).

fork_depth(H, [{H, _, _} | _], Depth) ->
	Depth;
fork_depth(H, [_ | BI], Depth) ->
	fork_depth(H, BI, Depth + 1).

%% @doc Test whether a new fork is 'preferable' to the current one.
%% The highest cumulated diff is the one with most work performed and should
%% therefor be prefered.
is_fork_preferable(ForkB, _, CurrentBI) when ForkB#block.height < ?FORK_1_6 ->
	ForkB#block.height > length(CurrentBI);
is_fork_preferable(ForkB, CurrentCDiff, _) ->
	ForkB#block.cumulative_diff > CurrentCDiff.

%% @doc Assign a priority to the task. 0 corresponds to the highest priority.
priority({gossip_message, #gs_msg{ data = {new_block, _, _, _, _, _} }}) ->
	0;
priority({fork_recovered, _, _, _}) ->
	1;
priority({work_complete, _, _, _, _, _}) ->
	2;
priority({gossip_message, #gs_msg{ data = {add_waiting_tx, _} }}) ->
	3;
priority(_) ->
	os:system_time(second).

%%%===================================================================
%%% Tests.
%%%===================================================================

get_diverged_block_hashes_test_() ->
	?assertEqual(
		{error, no_intersection},
		get_diverged_block_hashes(
			4,
			[bsh1, bsh2, bsh3, bsh4],
			[{h1, 0, <<>>}, {h2, 0, <<>>}, {h3, 0, <<>>}, {h4, 0, <<>>}]
		)
	),
	?assertEqual(
		{error, no_intersection},
		get_diverged_block_hashes(
			4,
			lists:seq(1, ?STORE_BLOCKS_BEHIND_CURRENT) ++ [h1, h2, h3, h4],
			[{h1, 0, <<>>}, {h2, 0, <<>>}, {h3, 0, <<>>}, {h4, 0, <<>>}]
		)
	),
	?assertEqual(
		{ok, {}},
		get_diverged_block_hashes(
			4,
			[h1, h2, h3, h4],
			[{h1, 0, <<>>}, {h2, 0, <<>>}, {h3, 0, <<>>}, {h4, 0, <<>>}]
		)
	),
	?assertEqual(
		{ok, {[h11], [{h2, 0, <<>>}, {h3, 0, <<>>}, {h4, 0, <<>>}]}},
		get_diverged_block_hashes(
			4,
			[h11, h2, h3, h4],
			[{h1, 0, <<>>}, {h2, 0, <<>>}, {h3, 0, <<>>}, {h4, 0, <<>>}]
		)
	),
	?assertEqual(
		{ok, {[h1, h2, h13], [{h4, 0, <<>>}]}},
		get_diverged_block_hashes(
			4,
			[h1, h2, h13, h4],
			[{h1, 0, <<>>}, {h2, 0, <<>>}, {h3, 0, <<>>}, {h4, 0, <<>>}]
		)
	).
