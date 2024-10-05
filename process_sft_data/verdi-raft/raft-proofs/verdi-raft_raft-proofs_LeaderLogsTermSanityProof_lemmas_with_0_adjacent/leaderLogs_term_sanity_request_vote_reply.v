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

Lemma leaderLogs_term_sanity_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_term_sanity.
Proof using ctgli rri.
term_sanity_start_update.
find_copy_apply_lem_hyp handleRequestVoteReply_type.
find_copy_apply_lem_hyp handleRequestVoteReply_log.
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; auto.
unfold ghost_data, raft_data in *.
simpl in *.
subst.
intuition; eauto; repeat find_rewrite; try discriminate.
find_apply_lem_hyp candidate_term_gt_log_lifted.
unfold candidate_term_gt_log in *.
simpl in *; repeat break_match; simpl in *.
unfold gt in *.
subst.
repeat find_rewrite.
eapply H3; auto.
