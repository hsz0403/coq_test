Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CandidateTermGtLogInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Section LeaderLogsTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {ctgli : candidate_term_gt_log_interface}.
Ltac term_sanity_start := red; unfold leaderLogs_term_sanity; simpl; intros.
Ltac term_sanity_start_update := term_sanity_start; repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
Ltac term_sanity_unchanged' lem := red; intros; eapply leaderLogs_term_sanity_unchanged; subst; eauto using lem.
Tactic Notation "term_sanity_unchanged" constr(lem) := term_sanity_unchanged' lem.
Tactic Notation "term_sanity_unchanged" := term_sanity_unchanged' eq_refl (* bogus *).
Ltac term_sanity_break_update := term_sanity_start_update; match goal with h : _ |- _ => eapply h end; [| eauto]; match goal with h : _ |- _ => solve [rewrite h; auto] end.
Ltac currentTerm_sanity_start := red; unfold leaderLogs_currentTerm_sanity; simpl; intros.
Ltac currentTerm_sanity_start_update := currentTerm_sanity_start; repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
Ltac currentTerm_sanity_unchanged := red; intros; eapply leaderLogs_currentTerm_sanity_unchanged; subst; eauto.
Ltac currentTerm_sanity_break_update := currentTerm_sanity_start_update; match goal with h : _ |- _ => eapply h end; [| eauto]; match goal with h : _ |- _ => solve [rewrite h; auto] end.
Ltac ctsc_start := red; unfold leaderLogs_currentTerm_sanity_candidate; simpl; intros.
Ltac ctsc_start_update := ctsc_start; repeat find_higher_order_rewrite; update_destruct; rewrite_update; [|eauto].
Ltac ctsc_unchanged := red; intros; eapply leaderLogs_currentTerm_sanity_candidate_unchanged; subst; eauto.
Instance lltsi : leaderLogs_term_sanity_interface.
Proof.
split.
-
apply leaderLogs_term_sanity_invariant.
-
apply leaderLogs_currentTerm_sanity_invariant.
-
apply leaderLogs_currentTerm_sanity_candidate_invariant.
End LeaderLogsTermSanity.

Lemma leaderLogs_currentTerm_sanity_candidate_append_entries : refined_raft_net_invariant_append_entries leaderLogs_currentTerm_sanity_candidate.
Proof using.
ctsc_unchanged.
-
apply update_elections_data_appendEntries_leaderLogs.
-
find_apply_lem_hyp handleAppendEntries_type_term.
intuition.
-
find_apply_lem_hyp handleAppendEntries_type_term.
intuition.
right.
congruence.
