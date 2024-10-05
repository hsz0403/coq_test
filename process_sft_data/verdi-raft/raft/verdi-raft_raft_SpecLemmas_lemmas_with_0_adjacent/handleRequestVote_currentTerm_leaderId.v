Require Import VerdiRaft.RaftState.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Section SpecLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Definition matchIndex_preserved st st' := type st' = Leader -> (type st = Leader /\ matchIndex st' = matchIndex st /\ log st' = log st).
Arguments matchIndex_preserved / _ _.
Definition matchIndex_preserved_except_at_host h st st' := type st' = Leader -> (type st = Leader /\ forall h', h <> h' -> (assoc_default name_eq_dec (matchIndex st') h' 0) = (assoc_default name_eq_dec (matchIndex st) h') 0).
Arguments matchIndex_preserved_except_at_host / _ _ _.
End SpecLemmas.

Lemma handleRequestVote_currentTerm_leaderId : forall h st t c li lt st' m, handleRequestVote h st t c li lt = (st', m) -> currentTerm st < currentTerm st' \/ (currentTerm st = currentTerm st' /\ leaderId st' = leaderId st).
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
repeat (break_match; try find_inversion; simpl in *; auto); do_bool; auto.
