Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.CandidateTermGtLogInterface.
Section CandidateTermGtLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {tsi : term_sanity_interface}.
Ltac start := red; unfold candidate_term_gt_log; simpl; intros; find_higher_order_rewrite; update_destruct; subst; rewrite_update; [|auto].
Instance ctgli : candidate_term_gt_log_interface.
Proof.
split.
apply candidate_term_gt_log_invariant.
End CandidateTermGtLog.

Lemma candidate_term_gt_log_timeout : raft_net_invariant_timeout candidate_term_gt_log.
Proof using tsi.
red.
unfold candidate_term_gt_log.
simpl.
intros.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_copy_apply_lem_hyp handleTimeout_log_same.
find_apply_lem_hyp handleTimeout_type_strong.
intuition.
+
repeat find_rewrite.
eauto.
+
find_apply_lem_hyp no_entries_past_current_term_invariant.
unfold no_entries_past_current_term in *.
intuition.
unfold no_entries_past_current_term_host in *.
repeat find_rewrite.
find_apply_hyp_hyp.
omega.
