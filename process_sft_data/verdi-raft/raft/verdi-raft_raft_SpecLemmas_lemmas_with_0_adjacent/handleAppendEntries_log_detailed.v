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

Theorem handleAppendEntries_log_detailed : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> (commitIndex st' = commitIndex st /\ log st' = log st) \/ (leaderId st' <> None /\ currentTerm st' = t /\ commitIndex st' = max (commitIndex st) (min ci (maxIndex es)) /\ es <> nil /\ pli = 0 /\ t >= currentTerm st /\ log st' = es /\ (findAtIndex (log st) (maxIndex es) = None \/ exists e, findAtIndex (log st) (maxIndex es) = Some e /\ eTerm e <> maxTerm es)) \/ (leaderId st' <> None /\ currentTerm st' = t /\ commitIndex st' = max (commitIndex st) (min ci (maxIndex (es ++ (removeAfterIndex (log st) pli)))) /\ es <> nil /\ exists e, In e (log st) /\ eIndex e = pli /\ eTerm e = plt) /\ t >= currentTerm st /\ log st' = es ++ (removeAfterIndex (log st) pli) /\ (findAtIndex (log st) (maxIndex es) = None \/ exists e, findAtIndex (log st) (maxIndex es) = Some e /\ eTerm e <> maxTerm es).
Proof using.
intros.
unfold handleAppendEntries in *.
break_if; [find_inversion; subst; eauto|].
break_if; [do_bool; break_if; find_inversion; subst; try find_apply_lem_hyp haveNewEntries_true; simpl in *; intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex, some_none, advanceCurrentTerm_term|].
simpl in *.
intuition eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex.
break_match; [|find_inversion; subst; eauto].
break_if; [find_inversion; subst; eauto|].
break_if; [|find_inversion; subst; eauto using advanceCurrentTerm_log, advanceCurrentTerm_commitIndex].
find_inversion; subst; simpl in *.
right.
right.
find_apply_lem_hyp findAtIndex_elim.
intuition; do_bool; find_apply_lem_hyp haveNewEntries_true; intuition eauto using advanceCurrentTerm_term; congruence.
