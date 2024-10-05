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

Lemma handleRequestVote_votedFor : forall pDst t cid lli llt d d' m, handleRequestVote pDst d t cid lli llt = (d', m) -> currentTerm d = currentTerm d' -> votedFor d = None \/ votedFor d = votedFor d'.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
repeat break_match; tuple_inversion; simpl in *; intuition; try discriminate; try solve [exfalso; do_bool; omega].
