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

Theorem handleAppendEntries_term_votedFor : forall h st t n pli plt es ci st' ps h', handleAppendEntries h st t n pli plt es ci = (st', ps) -> votedFor st' = Some h' -> currentTerm st' = currentTerm st /\ votedFor st' = votedFor st.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
repeat break_match; find_inversion; simpl in *; auto; congruence.
