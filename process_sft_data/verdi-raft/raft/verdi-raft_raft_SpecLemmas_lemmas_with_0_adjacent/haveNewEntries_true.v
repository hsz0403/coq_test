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

Lemma haveNewEntries_true : forall st es, haveNewEntries st es = true -> (es <> nil /\ (findAtIndex (log st) (maxIndex es) = None \/ exists e, findAtIndex (log st) (maxIndex es) = Some e /\ eTerm e <> maxTerm es)).
Proof using.
intros.
unfold haveNewEntries, not_empty in *.
repeat break_match; do_bool; intuition eauto; try congruence.
do_bool.
eauto.
