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

Lemma handleTimeout_messages: forall (out : list raft_output) (st : raft_data) (l : list (name * msg)) h (mi : logIndex) (mt : term) m st' t n, handleTimeout h st = (out, st', l) -> In m l -> snd m = RequestVote t n mi mt -> maxIndex (log st') = mi /\ maxTerm (log st') = mt /\ t = currentTerm st'.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; find_inversion; simpl in *; intuition; do_in_map; subst; simpl in *; find_inversion; auto.
