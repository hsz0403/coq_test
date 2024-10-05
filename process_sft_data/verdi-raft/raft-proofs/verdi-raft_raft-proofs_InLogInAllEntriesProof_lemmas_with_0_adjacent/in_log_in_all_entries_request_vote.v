Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.InLogInAllEntriesInterface.
Section InLogInAllEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Instance iliaei : in_log_in_all_entries_interface.
Proof.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply in_log_in_all_entries_init.
-
apply in_log_in_all_entries_client_request.
-
apply in_log_in_all_entries_timeout.
-
apply in_log_in_all_entries_append_entries.
-
apply in_log_in_all_entries_append_entries_reply.
-
apply in_log_in_all_entries_request_vote.
-
apply in_log_in_all_entries_request_vote_reply.
-
apply in_log_in_all_entries_do_leader.
-
apply in_log_in_all_entries_do_generic_server.
-
apply in_log_in_all_entries_state_same_packet_subset.
-
apply in_log_in_all_entries_reboot.
End InLogInAllEntries.

Lemma in_log_in_all_entries_request_vote : refined_raft_net_invariant_request_vote in_log_in_all_entries.
Proof using.
red.
unfold in_log_in_all_entries.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
rewrite update_elections_data_requestVote_allEntries.
find_erewrite_lem handleRequestVote_log.
eauto.
