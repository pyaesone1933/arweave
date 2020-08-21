-module(ar_node).

-export([
	start_link/1, start/7,
	stop/1,
	get_blocks/1,
	get_peers/1,
	get_block_index/1, get_height/1,
	get_trusted_peers/1, set_trusted_peers/2,
	get_balance/2,
	get_last_tx/2,
	get_wallets/2,
	get_wallet_list_chunk/3,
	get_current_diff/1, get_diff/1,
	get_pending_txs/1, get_pending_txs/2, get_mined_txs/1, is_a_pending_tx/2,
	get_current_block_hash/1, get_current_block/1,
	get_reward_addr/1,
	get_reward_pool/1,
	is_joined/1,
	get_block_txs_pairs/1,
	mine/1, automine/1,
	add_tx/2,
	cancel_tx/3,
	add_peers/2,
	print_reward_addr/0,
	set_reward_addr/2, set_reward_addr_from_file/1, generate_and_set_reward_addr/0,
	set_loss_probability/2, set_delay/2, set_mining_delay/2, set_xfer_speed/2,
	get_mempool_size/1
]).

-include("ar.hrl").

%%%===================================================================
%%% Public interface.
%%%===================================================================

%% @doc Start a node, linking to a supervisor process
start_link(Args) ->
	PID = erlang:apply(ar_node, start, Args),
	{ok, PID}.

%% @doc Start a node server.
start(Peers, BI, MiningDelay, RewardAddr, AutoJoin, Diff, LastRetarget) ->
	PID = spawn_link(
		fun() ->
			case {BI, AutoJoin} of
				{not_joined, true} ->
					ar_join:start(self(), Peers);
				_ ->
					do_nothing
			end,
			Gossip =
				ar_gossip:init(
					lists:filter(
						fun is_pid/1,
						Peers
					)
				),
			Height = ar_util:height_from_hashes(BI),
			{RewardPool, WeaveSize, Current, WalletList} =
				case BI of
					not_joined ->
						{0, 0, not_joined, not_set};
					[{H, _, _} | _] ->
						B = ar_storage:read_block(H),
						RecentBlockIndex = lists:sublist(BI, ?STORE_BLOCKS_BEHIND_CURRENT),
						{ok, _} =
							ar_wallets:start_link([
								{recent_block_index, RecentBlockIndex},
								{peers, Peers}
							]),
						{B#block.reward_pool, B#block.weave_size, H, B#block.wallet_list}
				end,
			%% Start processes, init state, and start server.
			NPid = self(),
			%% The message queue of this process may grow big under load.
			%% The flag makes VM store messages off heap and do not perform
			%% expensive GC on them.
			process_flag(message_queue_data, off_heap),
			process_flag(trap_exit, true),
			{ok, SPid} = ar_node_state:start_link(),
			{ok, WPid} = ar_node_worker:start(NPid, SPid),
			ok = ar_node_state:update(SPid, [
				{node, NPid},
				{gossip, Gossip},
				{block_index, BI},
				{current, Current},
				{wallet_list, WalletList},
				{mining_delay, MiningDelay},
				{reward_addr, RewardAddr},
				{reward_pool, RewardPool},
				{height, Height},
				{trusted_peers, Peers},
				{diff, Diff},
				{last_retarget, LastRetarget},
				{weave_size, WeaveSize},
				{block_txs_pairs, create_block_txs_pairs(BI)}
			]),
			server(SPid, WPid, queue:new())
		end
	),
	ar_http_iface_server:reregister(http_entrypoint_node, PID),
	PID.

%% @doc Stop a node server loop and its subprocesses.
stop(Node) ->
	Node ! stop,
	ok.

%% @doc Get the current top block.
get_current_block(PID) ->
	Ref = make_ref(),
	PID ! {get_current_block, self(), Ref},
	receive
		{Ref, block, CurrentBlock} -> CurrentBlock
	after ?LOCAL_NET_TIMEOUT ->
		not_found
	end.

%% @doc Return the entire blockindex from a node.
% TODO: Change references to blockindex, not blocklist.
% Code duplication against get_blockindex function.
get_blocks(Node) ->
	Ref = make_ref(),
	Node ! {get_blocks, self(), Ref},
	receive
		{Ref, blocks, Bs} -> Bs
	after ?LOCAL_NET_TIMEOUT ->
		not_found
	end.

%% @doc Gets the list of pending transactions. This includes:
%% 1. The transactions currently staying in the priority queue.
%% 2. The transactions on timeout waiting to be distributed around the network.
%% 3. The transactions ready to be and being mined.
get_pending_txs(Node) ->
	get_pending_txs(Node, []).

get_pending_txs(Node, Opts) ->
	Ref = make_ref(),
	Node ! {get_pending_txs, self(), Ref},
	receive
		{Ref, pending_txs, TXs} ->
			case lists:member(as_map, Opts) of
				true ->
					TXs;
				false ->
					case lists:member(id_only, Opts) of
						true ->
							maps:keys(TXs);
						false ->
							maps:fold(
								fun(_, {TX, _}, Acc) ->
									[TX | Acc]
								end,
								[],
								TXs
							)
					end
			end
	end.

is_a_pending_tx(Node, TXID) ->
	Ref = make_ref(),
	Node ! {get_pending_txs, self(), Ref},
	receive
		{Ref, pending_txs, TXs} ->
			maps:is_key(TXID, TXs)
	end.

%% @doc Gets the list of mined or ready to be mined transactions.
%% The list does _not_ include transactions in the priority queue or
%% those on timeout waiting for network propagation.
get_mined_txs(Node) ->
	Ref = make_ref(),
	Node ! {get_mined_txs, self(), Ref},
	receive
		{Ref, mined_txs, TXs} ->
			TXs
		after ?LOCAL_NET_TIMEOUT -> []
	end.

%% @doc Get the set of trusted peers.
%% The set of trusted peers is that in whcih where joined on.
get_trusted_peers(Proc) when is_pid(Proc) ->
	Ref = make_ref(),
	Proc ! {get_trusted_peers, self(), Ref},
	receive
		{Ref, peers, Ps} -> Ps
		after ?LOCAL_NET_TIMEOUT -> []
	end;
get_trusted_peers(_) ->
	unavailable.

%% @doc Set trusted peers.
set_trusted_peers(Proc, Peers) when is_pid(Proc) ->
	Proc ! {set_trusted_peers, Peers}.

%% @doc Get the list of peers from the nodes gossip state.
%% This is the list of peers that node will request blocks/txs from and will
%% distribute its mined blocks to.
get_peers(Proc) when is_pid(Proc) ->
	Ref = make_ref(),
	Proc ! {get_peers, self(), Ref},
	receive
		{Ref, peers, Ps} -> Ps
		after ?LOCAL_NET_TIMEOUT -> []
	end;
get_peers(Host) ->
	case ar_http_iface_client:get_peers(Host) of
		unavailable -> [];
		Peers -> Peers
	end.

get_block_index(Node) ->
	Ref = make_ref(),
	Node ! {get_blockindex, self(), Ref},
	receive
		{Ref, blockindex, not_joined} -> [];
		{Ref, blockindex, BI} -> BI
		after ?LOCAL_NET_TIMEOUT -> []
	end.

%% @doc Get the current block hash.
get_current_block_hash(Node) ->
	Ref = make_ref(),
	Node ! {get_current_block_hash, self(), Ref},
	receive
		{Ref, current_block_hash, not_joined} -> not_joined;
		{Ref, current_block_hash, Current} -> Current
		after ?LOCAL_NET_TIMEOUT -> unavailable
	end.

%% @doc Return the current height of the blockweave.
get_height(Node) ->
	Ref = make_ref(),
	Node ! {get_height, self(), Ref},
	receive
		{Ref, height, H} -> H
	after ?LOCAL_NET_TIMEOUT -> -1
	end.

%% @doc Check whether self node has joined the weave.
%% Uses blockindex value not_joined as witness.
is_joined(Node) ->
	Ref = make_ref(),
	Node ! {get_blockindex, self(), Ref},
	receive
		{Ref, blockindex, not_joined} -> false;
		{Ref, blockindex, _} -> true
	end.

%% @doc Get the current balance of a given wallet address.
%% The balance returned is in relation to the nodes current wallet list.
get_balance(Node, Addr) when ?IS_ADDR(Addr) ->
	Ref = make_ref(),
	Node ! {get_balance, self(), Ref, Addr},
	receive {Ref, balance, B} -> B end;
get_balance(Node, WalletID) ->
	get_balance(Node, ar_wallet:to_address(WalletID)).

%% @doc Get the last tx id associated with a given wallet address.
%% Should the wallet not have made a tx the empty binary will be returned.
get_last_tx(Node, Addr) when ?IS_ADDR(Addr) ->
	Ref = make_ref(),
	Node ! {get_last_tx, self(), Ref, Addr},
	receive {Ref, last_tx, LastTX} -> {ok, LastTX} end;
get_last_tx(Node, WalletID) ->
	get_last_tx(Node, ar_wallet:to_address(WalletID)).

get_wallets(Node, Addresses) ->
	Ref = make_ref(),
	Node ! {get_wallets, self(), Ref, Addresses},
	receive {Ref, wallets, Wallets} -> Wallets end.

get_wallet_list_chunk(Node, RootHash, Cursor) ->
	Ref = make_ref(),
	Node ! {get_wallet_list_chunk, self(), Ref, RootHash, Cursor},
	receive {Ref, wallet_list_chunk, Reply} -> Reply end.

%% @doc Returns the new difficulty of next mined block.
% TODO: Function name is confusing, returns the new difficulty being mined on,
% not the 'current' diff (that of the latest block)
get_current_diff(Node) ->
	Ref = make_ref(),
	Node ! {get_current_diff, self(), Ref},
	receive
		{Ref, current_diff, Diff} -> Diff
		after ?LOCAL_NET_TIMEOUT -> 1
	end.

%% @doc Returns the difficulty of the last successfully mined block.
%% Returns the difficulty of the current block (not of that being mined).
get_diff(Node) ->
	Ref = make_ref(),
	Node ! {get_diff, self(), Ref},
	receive
		{Ref, diff, Diff} -> Diff
		after ?LOCAL_NET_TIMEOUT -> 1
	end.

%% @doc Get the current rewardpool from the node.
get_reward_pool(Node) ->
	Ref = make_ref(),
	Node ! {get_reward_pool, self(), Ref},
	receive
		{Ref, reward_pool, RewardPool} -> RewardPool
		after ?LOCAL_NET_TIMEOUT -> 0
	end.

%% @doc Returns transaction identifiers from the last ?MAX_TX_ANCHOR_DEPTH
%% blocks grouped by block hash.
get_block_txs_pairs(Node) ->
	Ref = make_ref(),
	Node ! {get_block_txs_pairs, self(), Ref},
	receive
		{Ref, block_txs_pairs, BlockTXPairs} -> {ok, BlockTXPairs}
		after ?LOCAL_NET_TIMEOUT -> {error, timeout}
	end.

%% @doc Get the reward address attributed to the node.
%% This is the wallet address that should the node successfully mine a block
%% the reward will be credited to.
get_reward_addr(Node) ->
	Ref = make_ref(),
	Node ! {get_reward_addr, self(), Ref},
	receive
		{Ref, reward_addr, Addr} -> Addr
	after ?LOCAL_NET_TIMEOUT -> 0
	end.

%% @doc Set the reward address of the node.
%% This is the address mining rewards will be credited to.
set_reward_addr(Node, Addr) ->
	Node ! {set_reward_addr, Addr}.

%% @doc Set the reward address of the node from an Arweave keyfile.
%% This is the address mining rewards will be credited to.
set_reward_addr_from_file(Filepath) ->
	{_Priv, Pub} = ar_wallet:load(Filepath),
	set_reward_addr(whereis(http_entrypoint_node), ar_wallet:to_address(Pub)),
	ar:report(
		[
			{new_reward_address, ar_wallet:to_address(Pub)}
		]
	).

%% @doc Generate a new keyfile and set the reward address of the node to the
%% wallets address.
%% This is the address mining rewards wiwll be credited to.
generate_and_set_reward_addr() ->
	{_Priv, Pub} = ar_wallet:new(),
	set_reward_addr(whereis(http_entrypoint_node), ar_wallet:to_address(Pub)),
	ar:report(
		[
			{new_reward_address, ar_wallet:to_address(Pub)}
		]
	).

%% @doc Pretty print the reward address of the node.
print_reward_addr() ->
	ar_util:encode(get_reward_addr(whereis(http_entrypoint_node))).

%% @doc Trigger a node to start mining a block.
mine(Node) ->
	Node ! mine.

%% @doc Trigger a node to mine continually.
automine(Node) ->
	Node ! automine.

%% @doc Set the likelihood that a message will be dropped in transmission.
%% Used primarily for testing, simulating packet loss.
set_loss_probability(Node, Prob) ->
	Node ! {set_loss_probability, Prob}.

%% @doc Set the max network latency delay for a node.
%% Used primarily for testing, simulating transmission delays.
set_delay(Node, MaxDelay) ->
	Node ! {set_delay, MaxDelay}.

%% @doc Set the number of milliseconds to wait between hashes.
%% Used primarily for testing, simulating lower hasing power machine.
set_mining_delay(Node, Delay) ->
	Node ! {set_mining_delay, Delay}.

%% @doc Set the number of bytes the node can transfer in a second.
%% Used primarily for testing, simulating node connection strengths.
set_xfer_speed(Node, Speed) ->
	Node ! {set_xfer_speed, Speed}.

%% @doc Add a transaction to the node server loop.
%% If accepted the tx will enter the waiting pool before being mined into the
%% the next block.
add_tx(GS, TX) when is_record(GS, gs_state) ->
	{NewGS, _} = ar_gossip:send(GS, {add_tx, TX}),
	NewGS;
add_tx(Node, TX) when is_pid(Node) ->
	Node ! {add_tx, TX},
	ok;
add_tx({Node, Name} = Peer, TX) when is_atom(Node) andalso is_atom(Name) ->
	Peer ! {add_tx, TX},
	ok;
add_tx(Host, TX) ->
	ar_http_iface_client:send_new_tx(Host, TX).

%% @doc remove a TX from the waiting queues, with permission from the owner.
cancel_tx(Node, TXID, Sig) ->
	Node ! {cancel_tx, TXID, Sig}.

%% @doc Request to add a list of peers to the node server loop.
add_peers(Node, Peer) when not is_list(Peer) ->
	add_peers(Node, [Peer]);
add_peers(Node, Peers) ->
	%ar:d([{node, self()}, {requesting_add_peers, Peers}]),
	Node ! {add_peers, Peers},
	ok.

%% @doc Return memory pool size
get_mempool_size(Node) ->
	Ref = make_ref(),
	Node ! {get_mempool_size, self(), Ref},
	receive
		{Ref, get_mempool_size, Size} ->
			Size
		after ?LOCAL_NET_TIMEOUT ->
			0
	end.

%%%===================================================================
%%% Private functions.
%%%===================================================================

create_block_txs_pairs(not_joined) ->
	[];
create_block_txs_pairs(BI) ->
	create_block_txs_pairs(recent_blocks, lists:sublist(BI, 2 * ?MAX_TX_ANCHOR_DEPTH)).

create_block_txs_pairs(recent_blocks, []) ->
	[];
create_block_txs_pairs(recent_blocks, [{BH, _, _} | Rest]) ->
	B = ar_storage:read_block(BH),
	TXs = ar_storage:read_tx(B#block.txs),
	SizeTaggedTXs = ar_block:generate_size_tagged_list_from_txs(TXs),
	[{BH, SizeTaggedTXs} | create_block_txs_pairs(Rest)].

%% @doc Main server loop.
server(SPid, WPid, TaskQueue) ->
	receive
		stop ->
			% Stop the node server. First handle all open tasks
			% in the queue synchronously.
			% TODO mue: Possible race condition if worker is
			% currently processing one task! Also check order.
			{ok, Miner} = ar_node_state:lookup(SPid, miner),
			lists:foreach(fun(Task) ->
				ar_node_worker:call(WPid, Task)
			end, queue:to_list(TaskQueue)),
			case Miner of
				undefined -> do_nothing;
				PID		  -> ar_mine:stop(PID)
			end,
			ar_node_worker:stop(WPid),
			ar_node_state:stop(SPid),
			ok;
		{worker, Response} ->
			% Worker finished a task w/o errors.
			case Response of
				{error, Error} ->
					ar:err([{node_worker_error, {error, Error}}]);
				{ok, _} ->
					noop
			end,
			case queue:out(TaskQueue) of
				{empty, TaskQueue} ->
					% Empty queue, nothing to cast.
					server(SPid, WPid, TaskQueue);
				{{value, Task}, NewTaskQueue} ->
					% At least one task in queue, cast it to worker.
					ar_node_worker:cast(WPid, Task),
					server(SPid, WPid, NewTaskQueue)
			end;
		{'EXIT', _, _} ->
			ar_node_state:stop(SPid);
		Msg ->
			try handle(SPid, Msg) of
				{task, Task} ->
					% Handler returns worker task to do.
					case queue:is_empty(TaskQueue) of
						true ->
							% Queue is empty, directly cast task to worker.
							ar_node_worker:cast(WPid, Task),
							server(SPid, WPid, TaskQueue);
						false ->
							% Queue contains tasks, so add it.
							NewTaskQueue = queue:in(Task, TaskQueue),
							server(SPid, WPid, NewTaskQueue)
					end;
				ok ->
					% Handler is fine.
					server(SPid, WPid, TaskQueue)
			catch
				throw:Term ->
					ar:report([ {'NodeEXCEPTION', Term} ]),
					server(SPid, WPid, TaskQueue);
				exit:Term ->
					ar:report([ {'NodeEXIT', Term} ]),
					server(SPid, WPid, TaskQueue);
				error:Term:Stacktrace ->
					ar:report([ {'NodeERROR', {Term, Stacktrace}} ]),
					server(SPid, WPid, TaskQueue)
			end
	end.

%% @doc Handle the server messages. Returns {task, Task} or ok. First block
%% countains the state changing handler, second block the reading handlers.
handle(_SPid, Msg) when is_record(Msg, gs_msg) ->
	% We have received a gossip mesage. Gossip state manipulation
	% is always a worker task.
	{task, {gossip_message, Msg}};
handle(_SPid, {add_tx, TX}) ->
	{task, {add_tx, TX}};
handle(_SPid, {cancel_tx, TXID, Sig}) ->
	{task, {cancel_tx, TXID, Sig}};
handle(_SPid, {add_peers, Peers}) ->
	{task, {add_peers, Peers}};
handle(_SPid, {new_block, Peer, Height, NewB, BDS}) ->
	{task, {process_new_block, Peer, Height, NewB, BDS}};
handle(_SPid, {set_delay, MaxDelay}) ->
	{task, {set_delay, MaxDelay}};
handle(_SPid, {set_loss_probability, Prob}) ->
	{task, {set_loss_probability, Prob}};
handle(_SPid, {set_mining_delay, Delay}) ->
	{task, {set_mining_delay, Delay}};
handle(_SPid, {set_reward_addr, Addr}) ->
	{task, {set_reward_addr, Addr}};
handle(_SPid, {set_xfer_speed, Speed}) ->
	{task, {set_xfer_speed, Speed}};
handle(SPid, {work_complete, BaseBH, NewB, MinedTXs, BDS, POA, _HashesTried}) ->
	{ok, BI} = ar_node_state:lookup(SPid, block_index),
	case BI of
		not_joined ->
			ok;
		_ ->
			{task, {
				work_complete,
				BaseBH,
				NewB,
				MinedTXs,
				BDS,
				POA
			}}
	end;
handle(SPid, {fork_recovered, BI, BlockTXPairs, BaseH}) ->
	case BaseH of
		none ->
			{ok, Peers} = ar_node_state:lookup(SPid, trusted_peers),
			{ok, _} = ar_wallets:start_link([
				{recent_block_index, lists:sublist(BI, ?STORE_BLOCKS_BEHIND_CURRENT)},
				{peers, Peers}
			]);
		_ ->
			do_nothing
	end,
	{task, {fork_recovered, BI, BlockTXPairs, BaseH}};
handle(_SPid, mine) ->
	{task, mine};
handle(_SPid, automine) ->
	{task, automine};
%% ----- Getters and non-state-changing actions. -----
handle(SPid, {get_current_block, From, Ref}) ->
	{ok, BI} = ar_node_state:lookup(SPid, block_index),
	From ! {Ref, block, ar_util:get_head_block(BI)},
	ok;
handle(SPid, {get_blocks, From, Ref}) ->
	{ok, BI} = ar_node_state:lookup(SPid, block_index),
	From ! {Ref, blocks, BI},
	ok;
handle(SPid, {get_peers, From, Ref}) ->
	{ok, GS} = ar_node_state:lookup(SPid, gossip),
	From ! {Ref, peers, ar_gossip:peers(GS)},
	ok;
handle(SPid, {get_trusted_peers, From, Ref}) ->
	{ok, TrustedPeers} = ar_node_state:lookup(SPid, trusted_peers),
	From ! {Ref, peers, TrustedPeers},
	ok;
handle(SPid, {set_trusted_peers, Peers}) ->
	ar_node_state:update(SPid, [{trusted_peers, Peers}]);
handle(SPid, {get_blockindex, From, Ref}) ->
	{ok, BI} = ar_node_state:lookup(SPid, block_index),
	From ! {Ref, blockindex, BI},
	ok;
handle(SPid, {get_current_block_hash, From, Ref}) ->
	{ok, Res} = ar_node_state:lookup(SPid, current),
	From ! {Ref, current_block_hash, Res},
	ok;
handle(SPid, {get_height, From, Ref}) ->
	{ok, Height} = ar_node_state:lookup(SPid, height),
	From ! {Ref, height, Height},
	ok;
handle(_SPid, {get_balance, From, Ref, WalletID}) ->
	Balance = ar_wallets:get_balance(WalletID),
	From ! {Ref, balance, Balance},
	ok;
handle(_SPid, {get_last_tx, From, Ref, Addr}) ->
	LastTX = ar_wallets:get_last_tx(Addr),
	From ! {Ref, last_tx, LastTX},
	ok;
handle(_SPid, {get_wallets, From, Ref, Addresses}) ->
	Wallets = ar_wallets:get(Addresses),
	From ! {Ref, wallets, Wallets},
	ok;
handle(_SPid, {get_wallet_list_chunk, From, Ref, RootHash, Cursor}) ->
	From ! {Ref, wallet_list_chunk, ar_wallets:get_chunk(RootHash, Cursor)},
	ok;
handle(SPid, {get_pending_txs, From, Ref}) ->
	{ok, #{ txs := TXs }} = ar_node_state:lookup(SPid, [txs]),
	From ! {Ref, pending_txs, TXs},
	ok;
handle(SPid, {get_mined_txs, From, Ref}) ->
	{ok, #{ txs := TXs }} = ar_node_state:lookup(SPid, [txs]),
	MinedTXs = maps:fold(
		fun
			(_, {TX, ready_for_mining}, Acc) ->
				[TX | Acc];
			(_, _, Acc) ->
				Acc
		end,
		[],
		TXs
	),
	From ! {Ref, mined_txs, MinedTXs},
	ok;
handle(SPid, {get_current_diff, From, Ref}) ->
	{ok, #{
		height        := Height,
		diff          := Diff,
		last_retarget := LastRetarget
	}} = ar_node_state:lookup(SPid, [height, diff, last_retarget]),
	From ! {
		Ref,
		current_diff,
		ar_retarget:maybe_retarget(
			Height + 1,
			Diff,
			os:system_time(seconds),
			LastRetarget
		)
	},
	ok;
handle(SPid, {get_diff, From, Ref}) ->
	{ok, Diff} = ar_node_state:lookup(SPid, diff),
	From ! {Ref, diff, Diff},
	ok;
handle(SPid, {get_reward_pool, From, Ref}) ->
	{ok, RewardPool} = ar_node_state:lookup(SPid, reward_pool),
	From ! {Ref, reward_pool, RewardPool},
	ok;
handle(SPid, {get_reward_addr, From, Ref}) ->
	{ok, RewardAddr} = ar_node_state:lookup(SPid, reward_addr),
	From ! {Ref, reward_addr,RewardAddr},
	ok;
handle(SPid, {get_block_txs_pairs, From, Ref}) ->
	{ok, BlockTXPairs} = ar_node_state:lookup(SPid, block_txs_pairs),
	From ! {Ref, block_txs_pairs, BlockTXPairs},
	ok;
handle(SPid, {get_mempool_size, From, Ref}) ->
	{ok, #{ mempool_size := Size }} = ar_node_state:lookup(SPid, [mempool_size]),
	From ! {Ref, get_mempool_size, Size},
	ok;
handle(_Spid, {ar_node_state, _, _}) ->
	%% When an ar_node_state call times out its message may leak here. It can be huge so we avoid logging it.
	ok;
handle(_SPid, UnhandledMsg) ->
	ar:warn([{event, ar_node_received_unknown_message}, {message, UnhandledMsg}]),
	ok.
