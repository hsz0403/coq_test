Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Section CurrentTermGtZero.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance ctgzi : current_term_gt_zero_interface.
Proof.
split.
apply current_term_gt_zero_invariant.
End CurrentTermGtZero.

Lemma current_term_gt_zero_request_vote : raft_net_invariant_request_vote current_term_gt_zero.
Proof using.
unfold raft_net_invariant_request_vote, current_term_gt_zero.
simpl.
intuition.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update.
-
find_apply_lem_hyp handleRequestVote_type.
intuition.
repeat find_rewrite.
auto.
-
auto.
