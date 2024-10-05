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

Lemma handleAppendEntriesReply_nextIndex : forall h st st' m t es res h', handleAppendEntriesReply h st h' t es res = (st', m) -> type st' = Leader -> type st = Leader /\ ((nextIndex st' = nextIndex st \/ (res = true /\ currentTerm st = t /\ nextIndex st' = (assoc_set name_eq_dec (nextIndex st) h' (Nat.max (getNextIndex st h') (S (maxIndex es)))))) \/ (res = false /\ currentTerm st = t /\ nextIndex st' = (assoc_set name_eq_dec (nextIndex st) h' (pred (getNextIndex st h'))))).
Proof using.
unfold handleAppendEntriesReply, advanceCurrentTerm.
intros.
repeat break_match; repeat find_inversion; do_bool; simpl in *; intuition; congruence.
