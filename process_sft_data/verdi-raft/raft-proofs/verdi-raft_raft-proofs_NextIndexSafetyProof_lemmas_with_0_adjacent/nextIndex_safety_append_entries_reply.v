Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Section NextIndexSafety.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {si : sorted_interface}.
Definition nextIndex_preserved st st' := (type st' = Leader -> type st = Leader /\ maxIndex (log st) <= maxIndex (log st') /\ nextIndex st' = nextIndex st).
Instance nisi : nextIndex_safety_interface.
Proof.
split.
exact nextIndex_safety_invariant.
End NextIndexSafety.

Lemma nextIndex_safety_append_entries_reply : raft_net_invariant_append_entries_reply nextIndex_safety.
Proof using si aersi.
unfold raft_net_invariant_append_entries_reply, nextIndex_safety, getNextIndex.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
erewrite handleAppendEntriesReply_log by eauto.
find_copy_apply_lem_hyp handleAppendEntriesReply_nextIndex; auto.
intuition; repeat find_rewrite.
+
auto.
+
destruct (name_eq_dec h' (pSrc p)).
*
subst.
rewrite get_set_same_default.
unfold getNextIndex.
apply Max.max_case; auto.
{
destruct es; simpl.
*
omega.
*
pose proof append_entries_reply_sublog_invariant _ ltac:(eauto).
unfold append_entries_reply_sublog in *.
eapply_prop_hyp pBody pBody; simpl; eauto.
apply maxIndex_is_max; auto.
apply logs_sorted_invariant; auto.
}
*
rewrite get_set_diff_default by auto.
auto.
+
destruct (name_eq_dec h' (pSrc p)).
*
subst.
rewrite get_set_same_default.
unfold getNextIndex.
apply NPeano.Nat.le_le_pred.
auto.
*
rewrite get_set_diff_default by auto.
auto.
-
auto.
