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

Theorem handleClientRequest_matchIndex_maxIndex: forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> (maxIndex (log st') = maxIndex (log st) /\ matchIndex st' = matchIndex st) \/ (assoc_default name_eq_dec (matchIndex st') h 0) = maxIndex (log st').
Proof using.
intros.
unfold handleClientRequest in *.
break_match; find_inversion; subst; simpl in *; auto.
unfold assoc_default.
break_match; rewrite get_set_same in *; try congruence; find_inversion; auto.
