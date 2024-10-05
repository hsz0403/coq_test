Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.PrevLogCandidateEntriesTermInterface.
Section PrevLogCandidateEntriesTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {cti : cronies_term_interface}.
Context {cci : cronies_correct_interface}.
Instance plceti : prevLog_candidateEntriesTerm_interface.
Proof.
constructor.
apply prevLog_candidateEntriesTerm_invariant.
End PrevLogCandidateEntriesTerm.

Lemma prevLog_candidateEntriesTerm_do_leader : refined_raft_net_invariant_do_leader prevLog_candidateEntriesTerm.
Proof using cei.
unfold refined_raft_net_invariant_do_leader, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
find_apply_hyp_hyp.
eapply candidateEntriesTerm_ext; eauto.
eapply doLeader_preserves_candidateEntriesTerm; eauto.
-
find_apply_lem_hyp in_map_iff.
break_exists.
break_and.
subst.
simpl in *.
find_copy_eapply_lem_hyp doLeader_messages; eauto.
break_and.
intuition.
+
omega.
+
break_exists.
break_and.
red.
find_apply_lem_hyp candidate_entries_invariant.
unfold CandidateEntries, candidateEntries_host_invariant in *.
find_apply_lem_hyp findAtIndex_elim.
break_and.
match goal with | [ H : nwState ?net ?h = (?y, ?x) |- _ ] => replace (x) with (snd (nwState net h)) in * by (rewrite H; auto); replace (y) with (fst (nwState net h)) in * by (rewrite H; auto) end.
eapply_prop_hyp In In.
subst.
find_eapply_lem_hyp (doLeader_preserves_candidateEntries); eauto.
match goal with | [ H : nwState ?net ?h = (?y, ?x) |- _ ] => clear H end.
unfold candidateEntries in *.
break_exists_exists.
find_higher_order_rewrite.
update_destruct_simplify; auto.
