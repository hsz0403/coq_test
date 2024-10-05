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

Lemma in_any_log_term_was_created_request_vote : refined_raft_net_invariant_request_vote in_any_log_term_was_created.
Proof using.
red.
intros.
unfold in_any_log_term_was_created.
intros.
eapply term_was_created_preserved; [eapply_prop in_any_log_term_was_created|]; [| intros; simpl in *; repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto; rewrite leaderLogs_update_elections_data_requestVote; eauto].
iae_case.
-
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_apply_lem_hyp handleRequestVote_log.
repeat find_rewrite.
eauto.
-
find_eapply_lem_hyp handleRequestVote_no_append_entries.
find_apply_hyp_hyp.
intuition.
+
match goal with | _ : In ?p' (_ ++ _) |- _ => eapply in_aer with (p1 := p'); eauto end.
+
subst.
simpl in *.
find_false.
unfold mEntries in *.
break_match; try congruence.
subst.
repeat eexists; eauto.
-
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_rewrite_lem leaderLogs_update_elections_data_requestVote.
eauto.
