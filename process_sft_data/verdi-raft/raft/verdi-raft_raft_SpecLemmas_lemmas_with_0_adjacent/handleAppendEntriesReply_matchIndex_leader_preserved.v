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

Lemma handleAppendEntriesReply_matchIndex_leader_preserved: forall h st (d : raft_data) (m : list (name * msg)) (t : nat) (es : list entry) (res : bool) h', handleAppendEntriesReply h st h' t es res = (d, m) -> matchIndex_preserved_except_at_host h' st d.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
repeat (break_match; try find_inversion; simpl in *; auto); [|intros; congruence].
intros.
intuition.
unfold assoc_default.
repeat break_match; rewrite get_set_diff in *; repeat find_rewrite; congruence.
