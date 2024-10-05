Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonDefinitions.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Require Import VerdiRaft.EveryEntryWasCreatedInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section EveryEntryWasCreated.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lhlli : leaders_have_leaderLogs_interface}.
Hint Constructors in_any_log : core.
Definition in_any_log_term_was_created net := forall e, in_any_log net e -> term_was_created net (eTerm e).
Ltac iae_case := match goal with | [ H : in_any_log _ _ |- _ ] => invcs H end.
Ltac in_aer := repeat find_rewrite; eapply in_aer; eauto; repeat find_rewrite; reflexivity.
Ltac cr_in_log_in_leader_log := find_eapply_lem_hyp in_log; eapply_prop_hyp in_any_log_term_was_created in_any_log; unfold term_was_created in *; break_exists_exists; find_higher_order_rewrite; destruct_update; simpl in *; eauto; rewrite update_elections_data_client_request_leaderLogs; eauto.
Ltac cr_in_aer_in_leader_log := find_eapply_lem_hyp in_aer; eauto; eapply_prop_hyp in_any_log_term_was_created in_any_log; unfold term_was_created in *; break_exists_exists; find_higher_order_rewrite; destruct_update; simpl in *; eauto; rewrite update_elections_data_client_request_leaderLogs; eauto.
Ltac cr_in_ll_in_leader_log := find_eapply_lem_hyp in_ll; eauto; eapply_prop_hyp in_any_log_term_was_created in_any_log; unfold term_was_created in *; break_exists_exists; find_higher_order_rewrite; destruct_update; simpl in *; eauto; rewrite update_elections_data_client_request_leaderLogs; eauto.
Instance eewci : every_entry_was_created_interface.
split.
-
unfold every_entry_was_created.
intros.
apply in_any_log_term_was_created_invariant; eauto.
-
intros.
apply in_any_log_term_was_created_invariant; auto.
End EveryEntryWasCreated.

Lemma in_any_log_term_was_created_client_request : refined_raft_net_invariant_client_request in_any_log_term_was_created.
Proof using lhlli.
red.
intros.
unfold in_any_log_term_was_created.
intros.
iae_case.
-
unfold term_was_created.
simpl in *.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
+
find_apply_lem_hyp handleClientRequest_log.
intuition; subst; repeat find_rewrite; try cr_in_log_in_leader_log.
break_exists.
intuition.
repeat find_rewrite.
simpl in *.
intuition; subst.
*
find_eapply_lem_hyp leaders_have_leaderLogs_invariant; eauto.
match goal with | [h : name |- _ ] => (exists h) end.
break_exists_exists.
repeat find_rewrite.
repeat find_higher_order_rewrite.
rewrite update_eq; auto.
simpl.
rewrite update_elections_data_client_request_leaderLogs.
auto.
*
cr_in_log_in_leader_log.
+
cr_in_log_in_leader_log.
-
find_apply_hyp_hyp.
intuition.
+
cr_in_aer_in_leader_log.
+
do_in_map.
subst.
find_eapply_lem_hyp handleClientRequest_no_append_entries; eauto.
simpl in *.
intuition.
find_false.
unfold mEntries in *.
break_match; try congruence.
repeat eexists; eauto.
-
find_higher_order_rewrite.
destruct_update; simpl in *.
+
find_rewrite_lem update_elections_data_client_request_leaderLogs.
cr_in_ll_in_leader_log.
+
cr_in_ll_in_leader_log.
