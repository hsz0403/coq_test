Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.NoAppendEntriesRepliesToSelfInterface.
Require Import VerdiRaft.MatchIndexLeaderInterface.
Section MatchIndexLeader.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {naertsi : no_append_entries_replies_to_self_interface}.
Instance mili : match_index_leader_interface.
split.
intros.
apply raft_net_invariant; auto.
-
exact match_index_leader_init.
-
exact match_index_leader_client_request.
-
exact match_index_leader_timeout.
-
exact match_index_leader_append_entries.
-
exact match_index_leader_append_entries_reply.
-
exact match_index_leader_request_vote.
-
exact match_index_leader_request_vote_reply.
-
exact match_index_leader_do_leader.
-
exact match_index_leader_do_generic_server.
-
exact match_index_leader_state_same_packet_subset.
-
exact match_index_leader_reboot.
End MatchIndexLeader.

Lemma match_index_leader_init : raft_net_invariant_init match_index_leader.
Proof using.
red.
unfold match_index_leader in *.
simpl in *.
congruence.
