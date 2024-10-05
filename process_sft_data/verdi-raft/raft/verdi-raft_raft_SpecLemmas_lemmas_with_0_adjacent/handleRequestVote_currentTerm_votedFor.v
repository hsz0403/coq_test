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

Lemma handleRequestVote_currentTerm_votedFor : forall pDst t cid lli llt d d' m, handleRequestVote pDst d t cid lli llt = (d', m) -> (currentTerm d < currentTerm d' \/ (currentTerm d = currentTerm d' /\ votedFor d = None) \/ (currentTerm d = currentTerm d' /\ votedFor d = votedFor d')).
Proof using.
intros.
find_copy_apply_lem_hyp handleRequestVote_currentTerm_monotonic.
find_apply_lem_hyp le_lt_or_eq.
intuition.
right.
find_apply_lem_hyp handleRequestVote_votedFor; intuition.
