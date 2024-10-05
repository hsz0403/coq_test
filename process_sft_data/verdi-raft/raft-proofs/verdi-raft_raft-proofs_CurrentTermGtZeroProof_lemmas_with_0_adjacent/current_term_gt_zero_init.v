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

Lemma current_term_gt_zero_init : raft_net_invariant_init current_term_gt_zero.
Proof using.
unfold raft_net_invariant_init, current_term_gt_zero.
intros.
simpl in *.
congruence.
