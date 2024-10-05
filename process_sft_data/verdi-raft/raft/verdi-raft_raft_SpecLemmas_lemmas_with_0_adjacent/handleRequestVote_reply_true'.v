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

Lemma handleRequestVote_reply_true': forall (h : name) (h' : fin N) (st : RaftState.raft_data term name entry logIndex serverType data clientId output) (t lli llt : nat) (st' : raft_data) (t' : term), handleRequestVote h st t h' lli llt = (st', RequestVoteReply t' true) -> t' = t /\ currentTerm st' = t.
Proof using.
unfold handleRequestVote, advanceCurrentTerm in *.
intros.
repeat break_match; find_inversion; simpl in *; auto; try congruence; do_bool; try omega; eauto using le_antisym.
