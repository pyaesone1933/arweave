%%% @doc A directed acyclic graph with a single sink node. The sink node is supposed
%%% to store some big expensive to replicate entity (e.g., a wallet tree). Edges store
%%% diffs. To compute a representation of the entity corresponding to a particular vertice,
%%% one needs to walk from this vertice down to the sink node, collect all the diffs, and
%%% apply them in the reverse order.
-module(ar_diff_dag).

-export([
	new/3,
	get_sink/1,
	is_sink/2,
	is_node/2,
	add_node/5,
	update_leaf_source/3,
	update_sink/3,
	get_metadata/2,
	reconstruct/3,
	move_sink/4,
	filter/2
]).

-include_lib("eunit/include/eunit.hrl").

%%%===================================================================
%%% Public interface.
%%%===================================================================

%% @doc Create a new DAG with a sink node under the given identifier storing the given entity.
new(ID, Entity, Metadata) ->
	{#{ ID => {sink, Entity, Metadata} }, ID, #{ ID => sets:new() }}.

%% @doc Return the entity stored in the sink node.
get_sink(DAG) ->
	ID = element(2, DAG),
	element(2, maps:get(ID, element(1, DAG))).

%% @doc Return true if the given identifier is the identifier of the sink node.
is_sink({_Sinks, ID, _Sources}, ID) ->
	true;
is_sink(_DAG, _ID) ->
	false.

%% @doc Return true if the node with the given identifier exists.
is_node({Sinks, _Sink, _Sources}, ID) ->
	maps:is_key(ID, Sinks).

%% @doc Create a node with an edge connecting the given source and sink identifiers,
%% directed towards the given sink identifier.
%% If the node with given sink identifier does not exist or the node with the given source
%% identifier already exists, the call fails with a badkey exception.
add_node(DAG, SourceID, SinkID, Diff, Metadata) when SourceID /= SinkID ->
	assert_exists(SinkID, DAG),
	assert_not_exists(SourceID, DAG),
	{Sinks, Sink, Sources} = DAG,
	SinkSources = maps:get(SinkID, Sources, sets:new()),
	UpdatedSources = Sources#{
		SinkID => sets:add_element(SourceID, SinkSources),
		SourceID => sets:new()
	},
	{Sinks#{ SourceID => {SinkID, Diff, Metadata} }, Sink, UpdatedSources}.

%% @doc Update the given node via the given function of a diff and a metadata, which
%% returns a "new node identifier, new diff, new metadata" triplet. The node must be
%% a source (must have a sink) and a leaf (must be a sink for no node).
%% If the node does not exist or is not a leaf source, the call fails with a badkey exception.
update_leaf_source(DAG, ID, UpdateFun) ->
	assert_exists(ID, DAG),
	assert_not_sink(ID, DAG),
	{#{ ID := {SinkID, Diff, Metadata} } = Sinks, Sink, Sources} = DAG,
	case sets:is_empty(maps:get(ID, Sources, sets:new())) of
		false ->
			error({badkey, ID});
		true ->
			{NewID, UpdatedDiff, UpdatedMetadata} = UpdateFun(Diff, Metadata),
			Sinks2 = maps:remove(ID, Sinks),
			Sources2 = maps:remove(ID, Sources),
			Set = sets:add_element(NewID, sets:del_element(ID, maps:get(SinkID, Sources))),
			Sources3 = Sources2#{ SinkID => Set },
			{Sinks2#{ NewID => {SinkID, UpdatedDiff, UpdatedMetadata} }, Sink, Sources3}
	end.

%% @doc Update the sink via the given function of an entity and a metadata, which
%% returns a "new node identifier, new entity, new metadata" triplet.
%% If the node does not exist or is not a sink, the call fails with a badkey exception.
update_sink({Sinks, ID, Sources}, ID, UpdateFun) ->
	#{ ID := {sink, Entity, Metadata} } = Sinks,
	{NewID, NewEntity, NewMetadata} = UpdateFun(Entity, Metadata),
	Sinks2 = maps:remove(ID, Sinks),
	Sinks3 = Sinks2#{ NewID => {sink, NewEntity, NewMetadata} },
	{Set, Sources2} =
		case maps:take(ID, Sources) of
			error ->
				{sets:new(), Sources};
			Update ->
				Update
		end,
	Sinks4 = sets:fold(
		fun(SourceID, Acc) ->
			{ID, Diff, Meta} = maps:get(SourceID, Acc),
			Acc#{ SourceID => {NewID, Diff, Meta} }
		end,
		Sinks3,
		Set
	),
	Sources3 = Sources2#{ NewID => Set },
	{Sinks4, NewID, Sources3};
update_sink(_DAG, ID, _Fun) ->
	error({badkey, ID}).

%% @doc Return metadata stored at the given node.
%% If the node with given identifier does not exist, the call fails with a badkey exception.
get_metadata(DAG, ID) ->
	element(3, maps:get(ID, element(1, DAG))).

%% @doc Reconstruct the entity corresponding to the given node using
%% the given diff application function - a function of a diff and an entity.
%% If the node with given identifier does not exist, the call fails with a badkey exception.
reconstruct(DAG, ID, ApplyDiffFun) ->
	assert_exists(ID, DAG),
	reconstruct(DAG, ID, ApplyDiffFun, []).

%% @doc Make the given node the sink node. The diffs are reversed
%% according to the given function of a diff and an entity.
%% The new entity is constructed by applying the diffs on the path from the previous
%% sink to the new one using the given diff application function of a diff and an entity.
%% If the node with given identifier does not exist, the call fails with a badkey exception.
move_sink(DAG, ID, ApplyDiffFun, ReverseDiffFun) ->
	assert_exists(ID, DAG),
	move_sink(DAG, ID, ApplyDiffFun, ReverseDiffFun, []).

%% @doc Remove the nodes not passing the given filter and all the nodes flowing
%% into them from the given graph.
%% If the sink node falls under these conditions, the call fails with a badfilter exception.
%% The filter function is a function of a metadata, which returns true or false.
filter({Sinks, ID, Sources}, Fun) ->
	{ToRemove, Sources2} = filter(maps:iterator(Sinks), ID, Sources, Fun, sets:new()),
	{UpdatedSinks, UpdatedSources} = sets:fold(
		fun(RemoveID, {CurrentSinks, CurrentSources}) ->
			#{ RemoveID := {SinkID, _, _} } = CurrentSinks,
			CurrentSources2 =
				case sets:is_element(SinkID, ToRemove) of
					false ->
						Set = maps:get(SinkID, CurrentSources, sets:new()),
						maps:put(
							SinkID,
							sets:del_element(RemoveID, Set),
							CurrentSources
						);
					true ->
						CurrentSources
				end,
			{maps:remove(RemoveID, CurrentSinks), CurrentSources2}
		end,
		{Sinks, Sources2},
		ToRemove
	),
	{UpdatedSinks, ID, UpdatedSources}.

%%%===================================================================
%%% Private functions.
%%%===================================================================

assert_exists(ID, {Sinks, _, _}) ->
	case maps:is_key(ID, Sinks) of
		true ->
			ok;
		false ->
			error({badkey, ID})
	end.

assert_not_exists(ID, {Sinks, _, _}) ->
	case maps:is_key(ID, Sinks) of
		true ->
			error({badkey, ID});
		false ->
			ok
	end.

assert_not_sink(ID, {_, ID, _}) ->
	error({badkey, ID});
assert_not_sink(_ID, _DAG) ->
	ok.

reconstruct(DAG, ID, ApplyDiffFun, Diffs) ->
	case DAG of
		{#{ ID := {sink, Entity, _} }, ID, _} ->
			lists:foldl(ApplyDiffFun, Entity, Diffs);
		{#{ ID := {SinkID, Diff, _Metadata} }, _Sink, _Sinks} ->
			reconstruct(DAG, SinkID, ApplyDiffFun, [Diff | Diffs])
	end.

move_sink(DAG, ID, ApplyDiffFun, ReverseDiffFun, Diffs) ->
	case DAG of
		{#{ ID := {sink, Entity, Metadata} }, ID, _} ->
			{UpdatedSinkID, UpdatedEntity, UpdatedMetadata, UpdatedDAG} = lists:foldl(
				fun({SinkID, Diff, Meta}, {SourceID, CurrentEntity, CurrentMeta, CurrentDAG}) ->
					ReversedDiff = ReverseDiffFun(Diff, CurrentEntity),
					{Sinks, _, Sources} = CurrentDAG,
					Sinks2 = Sinks#{ SourceID => {SinkID, ReversedDiff, CurrentMeta} },
					SourceIDSet2 = sets:del_element(SinkID, maps:get(SourceID, Sources)),
					SinkIDSet2 =
						sets:add_element(SourceID, maps:get(SinkID, Sources, sets:new())),
					Sources2 = Sources#{ SinkID => SinkIDSet2, SourceID => SourceIDSet2 },
					{SinkID, ApplyDiffFun(Diff, CurrentEntity), Meta, {Sinks2, SinkID, Sources2}}
				end,
				{ID, Entity, Metadata, DAG},
				Diffs
			),
			{UpdatedSinks, UpdatedSinkID, UpdatedSources} = UpdatedDAG,
			UpdatedSinks2 = UpdatedSinks#{
				UpdatedSinkID => {sink, UpdatedEntity, UpdatedMetadata}
			},
			{UpdatedSinks2, UpdatedSinkID, UpdatedSources};
		{#{ ID := {SinkID, Diff, Metadata} }, _Sink, _Sinks} ->
			move_sink(DAG, SinkID, ApplyDiffFun, ReverseDiffFun, [{ID, Diff, Metadata} | Diffs])
	end.

filter(SinkIterator, SinkID, Sources, Fun, ToRemove) ->
	case maps:next(SinkIterator) of
		none ->
			{ToRemove, Sources};
		{ID, {_, _, Metadata}, NextIterator} ->
			case sets:is_element(ID, ToRemove) of
				true ->
					filter(NextIterator, SinkID, Sources, Fun, ToRemove);
				false ->
					case Fun(Metadata) of
						true ->
							filter(NextIterator, SinkID, Sources, Fun, ToRemove);
						false ->
							case ID == SinkID of
								true ->
									error(badfilter);
								false ->
									{Sources2, ToRemove2} =
										extend_with_subtree_identifiers(ID, {Sources, ToRemove}),
									filter(NextIterator, SinkID, Sources2, Fun, ToRemove2)
							end
					end
			end
	end.

extend_with_subtree_identifiers(ID, {Sources, ToRemove}) ->
	sets:fold(
		fun(RemoveID, Acc) ->
			extend_with_subtree_identifiers(RemoveID, Acc)
		end,
		{maps:remove(ID, Sources), sets:add_element(ID, ToRemove)},
		maps:get(ID, Sources, sets:new())
	).

%%%===================================================================
%%% Tests.
%%%===================================================================

diff_dag_test() ->
	%% node-1: {0, 1}
	DAG1 = new("node-1", 0, 1),
	?assertEqual(0, get_sink(DAG1)),
	?assertException(error, badfilter, filter(DAG1, fun(_) -> false end)),
	?assertEqual(DAG1, filter(DAG1, fun(Metadata) -> Metadata == 1 end)),
	?assertEqual(0, reconstruct(DAG1, "node-1", fun(_Diff, _Meta) -> not_called end)),
	?assertEqual(1, get_metadata(DAG1, "node-1")),
	%% node-1: {0, 1} <- node-2-1: {1, 2}
	DAG2 = add_node(DAG1, "node-2-1", "node-1", 1, 2),
	?assertEqual(0, get_sink(DAG2)),
	?assertEqual(DAG1, filter(DAG2, fun(Metadata) -> Metadata == 1 end)),
	?assertEqual(1, reconstruct(DAG2, "node-2-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(-1, reconstruct(DAG2, "node-2-1", fun(Diff, E) -> E - Diff end)),
	?assertEqual(1, get_metadata(DAG2, "node-1")),
	?assertEqual(2, get_metadata(DAG2, "node-2-1")),
	%% node-1: {0, 1} <- node-2-1: {2, 3}
	DAG3 = update_leaf_source(DAG2, "node-2-1", fun(D, M) -> {"node-2-1", D + 1, M + 1} end),
	?assertEqual(0, get_sink(DAG3)),
	?assertEqual(DAG1, filter(DAG3, fun(Metadata) -> Metadata == 1 end)),
	?assertEqual(2, reconstruct(DAG3, "node-2-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(3, get_metadata(DAG3, "node-2-1")),
	?assertException(error, {badkey, "node-1"}, update_leaf_source(DAG2, "node-1", not_called)),
	%% node-1: {0, 1} <- node-2-2: {1, 2}
	DAG4 = update_leaf_source(DAG3, "node-2-1", fun(D, M) -> {"node-2-2", D - 1, M - 1} end),
	?assertEqual(0, get_sink(DAG4)),
	?assertEqual(DAG1, filter(DAG4, fun(Metadata) -> Metadata == 1 end)),
	?assertEqual(1, reconstruct(DAG4, "node-2-2", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG4, "node-2-2")),
	?assertException(error, {badkey, "node-2-1"}, get_metadata(DAG4, "node-2-1")),
	%% node-1: {0, 1} <- node-2-2: {1, 2}
	%%                <- node-2-3: {2, 2}
	DAG5 = add_node(DAG4, "node-2-3", "node-1", 2, 2),
	?assertEqual(1, reconstruct(DAG5, "node-2-2", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, reconstruct(DAG5, "node-2-3", fun(Diff, E) -> E + Diff end)),
	%% node-1: {0, 1} <- node-2-2: {1, 2}
	%%                <- node-2-3: {2, 2} <- node-3-1: {-3, 3}
	DAG6 = add_node(DAG5, "node-3-1", "node-2-3", -3, 3),
	?assertEqual(1, reconstruct(DAG6, "node-2-2", fun(Diff, E) -> E + Diff end)),
	?assertEqual(-1, reconstruct(DAG6, "node-3-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(new("node-1", 0, 1), filter(DAG6, fun(Metadata) -> Metadata == 1 end)),
	%% node-1: {-2, 1} <- node-2-2: {1, 2}
	%%                 -> node-2-3: {3, 2} -> node-3-1: {-1, 3}
	DAG7 = move_sink(DAG6, "node-3-1", fun(Diff, E) -> E + Diff end, fun(Diff, _E) -> -Diff end),
	?assertEqual(-1, get_sink(DAG7)),
	?assertEqual(1, reconstruct(DAG7, "node-2-2", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG7, "node-2-2")),
	?assertEqual(0, reconstruct(DAG7, "node-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(1, get_metadata(DAG7, "node-1")),
	?assertEqual(2, reconstruct(DAG7, "node-2-3", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG7, "node-2-3")),
	?assertEqual(-1, reconstruct(DAG7, "node-3-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(3, get_metadata(DAG7, "node-3-1")),
	ExpectedFilteredDAG7 = add_node(new("node-3-1", -1, 3), "node-2-3", "node-3-1", 3, 2),
	?assertEqual(ExpectedFilteredDAG7, filter(DAG7, fun(Metadata) -> Metadata >= 2 end)),
	%%  node-2-3: {3, 2} -> node-3-1: {-1, 3}
	DAG8 = filter(DAG7, fun(Metadata) -> Metadata >= 2 end),
	?assertEqual(-1, get_sink(DAG8)),
	?assertEqual(2, get_metadata(DAG8, "node-2-3")),
	?assertEqual(3, get_metadata(DAG8, "node-3-1")),
	?assertException(error, {badkey, "node-1"}, get_metadata(DAG8, "node-1")),
	?assertException(error, {badkey, "node-2-2"}, get_metadata(DAG8, "node-2-2")),
	%% node-1: {-1, 1} -> node-2-2: {1, 2}
	%%                 <- node-2-3: {2, 2} <- node-3-1: {-3, 3}
	DAG9 = move_sink(DAG7, "node-2-2", fun(Diff, E) -> E + Diff end, fun(Diff, _E) -> -Diff end),
	?assertEqual(1, get_sink(DAG9)),
	?assertEqual(0, reconstruct(DAG9, "node-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(1, get_metadata(DAG9, "node-1")),
	?assertEqual(2, reconstruct(DAG9, "node-2-3", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG9, "node-2-3")),
	?assertEqual(-1, reconstruct(DAG9, "node-3-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(3, get_metadata(DAG9, "node-3-1")),
	?assertEqual(new("node-2-2", 1, 2), filter(DAG9, fun(Metadata) -> Metadata == 2 end)),
	%% node-1: {-1, 1} -> node-2-2: {1, 2} <- node-3-2: {10, 3}
	%%                 <- node-2-3: {2, 2} <- node-3-1: {-3, 3}
	DAG10 = add_node(DAG9, "node-3-2", "node-2-2", 10, 3),
	%% node-1: {-1, 1} -> node-2-2: {-10, 2} -> node-3-2: {11, 3}
	%%                 <- node-2-3: {2, 2} <- node-3-1: {-3, 3}
	DAG11 = move_sink(DAG10, "node-3-2", fun(Diff, E) -> E + Diff end, fun(Diff, _E) -> -Diff end),
	?assertEqual(11, get_sink(DAG11)),
	?assertEqual(1, reconstruct(DAG11, "node-2-2", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG11, "node-2-2")),
	?assertEqual(0, reconstruct(DAG11, "node-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(1, get_metadata(DAG11, "node-1")),
	?assertEqual(2, reconstruct(DAG11, "node-2-3", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG11, "node-2-3")),
	?assertEqual(-1, reconstruct(DAG11, "node-3-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(3, get_metadata(DAG11, "node-3-1")),
	?assertException(
		error, {badkey, "node-2-2"},
		update_leaf_source(DAG11, "node-2-2", fun(_Diff, _Meta) -> not_called end)
	),
	%% node-1: {-1, 1} -> node-2-2: {-10, 2} -> node-3-2: {12, 3}
	%%                 <- node-2-3: {2, 2} <- node-3-1: {-3, 3}
	DAG12 = update_sink(DAG11, "node-3-2", fun(11, 3) -> {"node-3-2", 12, 3} end),
	?assertEqual(12, get_sink(DAG12)),
	?assertEqual(3, get_metadata(DAG12, "node-3-2")),
	?assertEqual(2, reconstruct(DAG12, "node-2-2", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG12, "node-2-2")),
	?assertEqual(1, reconstruct(DAG12, "node-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(1, get_metadata(DAG12, "node-1")),
	?assertEqual(3, reconstruct(DAG12, "node-2-3", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG12, "node-2-3")),
	?assertEqual(0, reconstruct(DAG12, "node-3-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(3, get_metadata(DAG12, "node-3-1")),
	?assertException(error, {badkey, "node-2-2"}, update_sink(DAG11, "node-2-2", not_called)),
	?assertException(error, {badkey, "node-3-1"}, update_sink(DAG11, "node-3-1", not_called)),
	%% node-1: {-1, 1} -> node-2-2: {-10, 2} -> new-node-3-2: {13, 3}
	%%                 <- node-2-3: {2, 2} <- node-3-1: {-3, 3}
	DAG13 = update_sink(DAG12, "node-3-2", fun(12, 3) -> {"new-node-3-2", 13, 3} end),
	?assertEqual(13, get_sink(DAG13)),
	?assertEqual(3, get_metadata(DAG13, "new-node-3-2")),
	?assertException(error, {badkey, "node-3-2"}, get_metadata(DAG13, "node-3-2")),
	?assertEqual(3, reconstruct(DAG13, "node-2-2", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG13, "node-2-2")),
	?assertEqual(2, reconstruct(DAG13, "node-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(1, get_metadata(DAG13, "node-1")),
	?assertEqual(4, reconstruct(DAG13, "node-2-3", fun(Diff, E) -> E + Diff end)),
	?assertEqual(2, get_metadata(DAG13, "node-2-3")),
	?assertEqual(1, reconstruct(DAG13, "node-3-1", fun(Diff, E) -> E + Diff end)),
	?assertEqual(3, get_metadata(DAG13, "node-3-1")),
	%% node-1: {0, 1} <- node-2: {1, 2}
	DAG14 = add_node(new("node-1", 0, 1), "node-2", "node-1", 1, 2),
	?assertEqual(0, get_sink(DAG14)),
	?assertEqual(1, reconstruct(DAG14, "node-2", fun(Diff, E) -> E + Diff end)),
	%% node-1: {-1, 1} -> node-2: {1, 2}
	DAG15 = move_sink(DAG14, "node-2", fun(Diff, E) -> E + Diff end, fun(Diff, _E) -> -Diff end),
	?assertEqual(1, get_sink(DAG15)),
	?assertEqual(0, reconstruct(DAG15, "node-1", fun(Diff, E) -> E + Diff end)),
	?assertException(error, {badkey, "node-2"}, add_node(DAG15, "node-2", "node-1", 1, 2)),
	?assertException(error, {badkey, "node-1"}, add_node(DAG15, "node-1", "node-2", 1, 2)).
