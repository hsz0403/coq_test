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

Lemma nextIndex_safety_preserved : forall st st', (forall h', type st = Leader -> Nat.pred (getNextIndex st h') <= maxIndex (log st)) -> nextIndex_preserved st st' -> (forall h', type st' = Leader -> Nat.pred (getNextIndex st' h') <= maxIndex (log st')).
Proof using.
unfold getNextIndex, nextIndex_preserved in *.
intuition.
repeat find_rewrite.
auto.
unfold assoc_default in *.
specialize (H h').
break_match.
-
eauto using le_trans.
-
Admitted.

Theorem handleClientRequest_nextIndex_preserved : forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> nextIndex_preserved st st'.
Proof using.
unfold handleClientRequest, nextIndex_preserved.
intros.
repeat break_match; repeat find_inversion; simpl in *; try congruence.
Admitted.

Lemma nextIndex_safety_client_request : raft_net_invariant_client_request nextIndex_safety.
Proof using.
unfold raft_net_invariant_client_request, nextIndex_safety.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
eauto using nextIndex_safety_preserved, handleClientRequest_nextIndex_preserved.
-
Admitted.

Lemma handleTimeout_nextIndex_preserved : forall h d out d' l, handleTimeout h d = (out, d', l) -> nextIndex_preserved d d'.
Proof using.
unfold handleTimeout, tryToBecomeLeader, nextIndex_preserved.
intros.
repeat break_match; repeat find_inversion; simpl in *; try congruence.
Admitted.

Lemma nextIndex_safety_timeout : raft_net_invariant_timeout nextIndex_safety.
Proof using.
unfold raft_net_invariant_timeout, nextIndex_safety.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
eauto using nextIndex_safety_preserved, handleTimeout_nextIndex_preserved.
-
Admitted.

Lemma handleAppendEntries_nextIndex_preserved : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> nextIndex_preserved st st'.
Proof using.
unfold handleAppendEntries, nextIndex_preserved, advanceCurrentTerm.
intros.
Admitted.

Lemma nextIndex_safety_append_entries : raft_net_invariant_append_entries nextIndex_safety.
Proof using.
unfold raft_net_invariant_append_entries, nextIndex_safety.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
eauto using nextIndex_safety_preserved, handleAppendEntries_nextIndex_preserved.
-
Admitted.

Lemma handleAppendEntriesReply_nextIndex : forall h st st' m t es res h', handleAppendEntriesReply h st h' t es res = (st', m) -> type st' = Leader -> type st = Leader /\ ((nextIndex st' = nextIndex st \/ (res = true /\ currentTerm st = t /\ nextIndex st' = (assoc_set name_eq_dec (nextIndex st) h' (Nat.max (getNextIndex st h') (S (maxIndex es)))))) \/ (res = false /\ currentTerm st = t /\ nextIndex st' = (assoc_set name_eq_dec (nextIndex st) h' (pred (getNextIndex st h'))))).
Proof using.
unfold handleAppendEntriesReply, advanceCurrentTerm.
intros.
Admitted.

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
Admitted.

Lemma handleRequestVote_nextIndex_preserved : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> nextIndex_preserved st st'.
Proof using.
unfold handleRequestVote, nextIndex_preserved, advanceCurrentTerm.
intros.
Admitted.

Lemma nextIndex_safety_init : raft_net_invariant_init nextIndex_safety.
Proof using.
unfold raft_net_invariant_init, nextIndex_safety.
intros.
discriminate.
