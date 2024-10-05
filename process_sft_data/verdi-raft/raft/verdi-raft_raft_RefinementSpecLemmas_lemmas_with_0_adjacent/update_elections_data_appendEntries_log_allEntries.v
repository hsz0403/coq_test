Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Section SpecLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
End SpecLemmas.

Lemma update_elections_data_appendEntries_log_allEntries : forall h st t n pli plt es ci st' h' ps, handleAppendEntries h (snd st) t n pli plt es ci = (st', ps) -> (log st' = log (snd st) /\ allEntries (update_elections_data_appendEntries h st t h' pli plt es ci) = allEntries (fst st)) \/ (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci) = (map (fun e => (t, e)) es) ++ allEntries (fst st) /\ ((currentTerm st' = t /\ log st' = log (snd st) /\ haveNewEntries (snd st) es = false) \/ (currentTerm st' = t /\ currentTerm (snd st) <= t /\ es <> [] /\ pli = 0 /\ log st' = es) \/ (currentTerm st' = t /\ currentTerm (snd st) <= t /\ es <> [] /\ pli <> 0 /\ exists e, In e (log (snd st)) /\ eIndex e = pli /\ eTerm e = plt) /\ log st' = es ++ (removeAfterIndex (log (snd st)) pli))).
Proof using.
intros.
unfold update_elections_data_appendEntries, handleAppendEntries in *.
repeat break_match; repeat find_inversion; auto; simpl in *.
-
right.
intuition.
right.
left.
do_bool.
intuition; eauto using advanceCurrentTerm_term.
find_apply_lem_hyp haveNewEntries_not_empty.
congruence.
-
rewrite advanceCurrentTerm_log.
right.
intuition.
left.
intuition.
do_bool.
eauto using advanceCurrentTerm_term.
-
right.
intuition.
right.
right.
do_bool.
intuition.
+
eauto using advanceCurrentTerm_term.
+
find_apply_lem_hyp haveNewEntries_not_empty.
congruence.
+
find_apply_lem_hyp findAtIndex_elim.
intuition; do_bool; eauto.
-
rewrite advanceCurrentTerm_log.
do_bool.
rewrite advanceCurrentTerm_term; auto.
intuition.
