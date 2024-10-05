Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section MatchIndexSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {si : sorted_interface}.
Instance matchisi : match_index_sanity_interface.
Proof.
split.
exact match_index_sanity_invariant.
End MatchIndexSanity.

Lemma match_index_sanity_invariant : forall net, raft_intermediate_reachable net -> match_index_sanity net.
Proof using si aersi.
intros.
apply raft_net_invariant; auto.
-
apply match_index_sanity_init.
-
apply match_index_sanity_client_request.
-
apply match_index_sanity_timeout.
-
apply match_index_sanity_append_entries.
-
apply match_index_sanity_append_entries_reply.
-
apply match_index_sanity_request_vote.
-
apply match_index_sanity_request_vote_reply.
-
apply match_index_sanity_do_leader.
-
apply match_index_sanity_do_generic_server.
-
apply match_index_sanity_state_same_packet_subset.
-
apply match_index_sanity_reboot.
