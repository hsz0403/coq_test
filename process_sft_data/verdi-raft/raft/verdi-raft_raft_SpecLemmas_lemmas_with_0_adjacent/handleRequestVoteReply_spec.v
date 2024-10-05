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

Lemma handleRequestVoteReply_spec : forall h st h' t r st', st' = handleRequestVoteReply h st h' t r -> log st' = log st /\ (forall v, In v (votesReceived st) -> In v (votesReceived st')) /\ ((currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' <> Candidate) /\ (type st <> Leader /\ type st' = Leader -> (type st = Candidate /\ wonElection (dedup name_eq_dec (votesReceived st')) = true)).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
repeat break_match; try find_inversion; subst; simpl in *; intuition; do_bool; intuition; try right; congruence.
