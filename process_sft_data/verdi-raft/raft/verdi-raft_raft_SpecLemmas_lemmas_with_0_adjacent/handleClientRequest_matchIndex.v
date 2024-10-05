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

Theorem handleClientRequest_matchIndex : forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> (maxIndex (log st') = maxIndex (log st) /\ matchIndex st' = matchIndex st) \/ matchIndex st' = assoc_set name_eq_dec (matchIndex st) h (maxIndex (log st')) /\ maxIndex (log st') = S (maxIndex (log st)).
Proof using.
unfold handleClientRequest.
intros.
repeat break_match; repeat find_inversion; auto.
