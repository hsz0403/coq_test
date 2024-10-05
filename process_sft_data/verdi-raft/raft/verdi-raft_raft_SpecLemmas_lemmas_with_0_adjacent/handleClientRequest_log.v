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

Theorem handleClientRequest_log : forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> ps = [] /\ (log st' = log st \/ exists e, log st' = e :: log st /\ eIndex e = S (maxIndex (log st)) /\ eTerm e = currentTerm st /\ eClient e = client /\ eInput e = c /\ eId e = id /\ type st = Leader).
Proof using.
intros.
unfold handleClientRequest in *.
break_match; find_inversion; subst; intuition.
simpl in *.
eauto 10.
