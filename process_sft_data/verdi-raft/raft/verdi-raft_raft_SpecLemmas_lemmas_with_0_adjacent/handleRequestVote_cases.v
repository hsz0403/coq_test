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

Lemma handleRequestVote_cases : forall h h' t lli llt st st' m, handleRequestVote h st t h' lli llt = (st', m) -> st' = st \/ st' = advanceCurrentTerm st t \/ (st' = {[ advanceCurrentTerm st t with votedFor := Some h']} /\ (votedFor st = None /\ currentTerm st = t \/ currentTerm st < t)).
Proof using.
unfold handleRequestVote.
intros.
repeat break_match; repeat find_inversion; intuition.
-
simpl in *.
discriminate.
-
unfold advanceCurrentTerm in *.
break_if; simpl in *; do_bool; intuition.
