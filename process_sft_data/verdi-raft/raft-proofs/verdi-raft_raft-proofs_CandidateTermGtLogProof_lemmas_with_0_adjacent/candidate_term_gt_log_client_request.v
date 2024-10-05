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

Lemma candidate_term_gt_log_client_request : raft_net_invariant_client_request candidate_term_gt_log.
Proof using.
red.
unfold candidate_term_gt_log.
simpl.
intros.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_copy_apply_lem_hyp handleClientRequest_type.
find_apply_lem_hyp handleClientRequest_log.
intuition.
+
repeat find_rewrite.
eauto.
+
break_exists.
intuition.
repeat find_rewrite.
discriminate.
