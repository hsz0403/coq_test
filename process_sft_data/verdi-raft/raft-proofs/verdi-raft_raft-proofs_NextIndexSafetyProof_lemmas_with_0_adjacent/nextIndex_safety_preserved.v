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
omega.
