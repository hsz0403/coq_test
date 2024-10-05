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

Lemma doLeader_preserves_candidateEntriesTerm : forall net gd d h os d' ms t', nwState net h = (gd, d) -> doLeader d h = (os, d', ms) -> candidateEntriesTerm t' (nwState net) -> candidateEntriesTerm t' (update name_eq_dec (nwState net) h (gd, d')).
Proof using.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
break_and.
update_destruct_simplify; auto.
split.
-
match goal with | [ H : nwState ?net ?h = (?x, _) |- _ ] => replace (x) with (fst (nwState net h)) in * by (rewrite H; auto) end.
intuition.
-
match goal with | [ H : nwState ?net ?h = (_, ?x) |- _ ] => replace (x) with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
find_apply_lem_hyp doLeader_type.
intuition.
subst.
repeat find_rewrite.
auto.
