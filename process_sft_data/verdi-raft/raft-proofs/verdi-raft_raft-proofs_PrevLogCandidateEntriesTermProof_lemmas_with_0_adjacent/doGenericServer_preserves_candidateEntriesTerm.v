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

Lemma doGenericServer_preserves_candidateEntriesTerm : forall net gd d h os d' ms t, nwState net h = (gd, d) -> doGenericServer h d = (os, d', ms) -> candidateEntriesTerm t (nwState net) -> candidateEntriesTerm t (update name_eq_dec (nwState net) h (gd, d')).
Proof using.
intros.
find_apply_lem_hyp doGenericServer_type.
break_and.
eapply candidateEntriesTerm_same; eauto.
-
intros.
update_destruct_simplify; auto.
find_rewrite.
simpl.
auto.
-
intros.
update_destruct_simplify; auto.
repeat find_rewrite.
auto.
-
intros.
update_destruct_simplify; auto.
repeat find_rewrite.
auto.
