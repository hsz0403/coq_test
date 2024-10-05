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

Lemma handleRV_advanceCurrentTerm_preserves_candidateEntriesTerm : forall net h h' t lli llt t', candidateEntriesTerm t' (nwState net) -> candidateEntriesTerm t' (update name_eq_dec (nwState net) h (update_elections_data_requestVote h h' t h' lli llt (nwState net h), advanceCurrentTerm (snd (nwState net h)) t)).
Proof using.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
update_destruct_simplify; intuition.
-
now rewrite update_elections_data_requestVote_cronies_same.
-
intros.
match goal with | [ H : context [advanceCurrentTerm ?st ?t] |- _ ] => pose proof advanceCurrentTerm_same_or_type_follower st t end.
intuition.
+
repeat find_rewrite.
auto.
+
congruence.
