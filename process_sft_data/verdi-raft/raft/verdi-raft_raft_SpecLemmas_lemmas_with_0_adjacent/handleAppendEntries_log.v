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

Theorem handleAppendEntries_log : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> log st' = log st \/ (currentTerm st <= t /\ es <> [] /\ pli = 0 /\ log st' = es) \/ (currentTerm st <= t /\ es <> [] /\ pli <> 0 /\ exists e, In e (log st) /\ eIndex e = pli /\ eTerm e = plt) /\ log st' = es ++ (removeAfterIndex (log st) pli).
Proof using.
intros.
unfold handleAppendEntries in *.
break_if; [find_inversion; subst; eauto|].
break_if; [do_bool; break_if; find_inversion; subst; try find_apply_lem_hyp haveNewEntries_not_empty; intuition; simpl in *; eauto using advanceCurrentTerm_log|].
break_if.
-
break_match; [|find_inversion; subst; eauto].
break_if; [find_inversion; subst; eauto|].
find_inversion; subst; simpl in *.
right.
right.
find_apply_lem_hyp findAtIndex_elim.
intuition; do_bool; eauto.
find_apply_lem_hyp haveNewEntries_not_empty.
congruence.
-
repeat break_match; find_inversion; subst; eauto.
simpl in *.
eauto using advanceCurrentTerm_log.
