Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section MatchIndexSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {si : sorted_interface}.
Instance matchisi : match_index_sanity_interface.
Proof.
split.
exact match_index_sanity_invariant.
End MatchIndexSanity.

Lemma match_index_sanity_append_entries_reply : raft_net_invariant_append_entries_reply match_index_sanity.
Proof using si aersi.
unfold raft_net_invariant_append_entries_reply, match_index_sanity.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
erewrite handleAppendEntriesReply_log by eauto.
find_copy_apply_lem_hyp handleAppendEntriesReply_matchIndex; auto.
intuition.
+
repeat find_rewrite.
auto.
+
repeat find_rewrite.
destruct (name_eq_dec h (pSrc p)).
*
subst.
rewrite get_set_same_default.
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
-
auto.
