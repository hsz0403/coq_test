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

Lemma doLeader_message_entries : forall st h os st' ms m t n pli plt es ci e, doLeader st h = (os, st', ms) -> In m ms -> snd m = AppendEntries t n pli plt es ci -> In e es -> In e (log st).
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
break_match; try solve [find_inversion; simpl in *; intuition].
break_if; try solve [find_inversion; simpl in *; intuition].
find_inversion.
simpl.
do_in_map.
subst.
simpl in *.
find_inversion.
eauto using findGtIndex_in.
