Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Section TermsAndIndicesFromOneLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {ctgzi : current_term_gt_zero_interface}.
Definition terms_and_indices_from_one_log_ind (net : network) : Prop := terms_and_indices_from_one_log net /\ terms_and_indices_from_one_log_nw net.
Instance taifoli : terms_and_indices_from_one_log_interface.
Proof.
split.
-
apply terms_and_indices_from_one_log_ind_invariant.
-
apply terms_and_indices_from_one_log_ind_invariant.
End TermsAndIndicesFromOneLog.

Lemma terms_and_indices_from_one_log_ind_append_entries : raft_net_invariant_append_entries terms_and_indices_from_one_log_ind.
Proof using.
red.
unfold terms_and_indices_from_one_log_ind.
split; red; simpl in *; intuition.
-
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; auto.
find_apply_lem_hyp handleAppendEntries_log.
intuition.
+
find_rewrite.
auto.
+
subst.
unfold terms_and_indices_from_one_log_nw in *.
eauto.
+
break_exists.
intuition.
subst.
find_rewrite.
apply terms_and_indices_from_one_app.
*
eauto.
*
eapply terms_and_indices_from_one_In; [eapply removeAfterIndex_in | eauto].
-
unfold terms_and_indices_from_one_log_nw in *.
find_apply_hyp_hyp.
intuition; eauto.
find_apply_lem_hyp handleAppendEntries_not_append_entries.
exfalso.
apply H.
repeat eexists.
subst.
eauto.
