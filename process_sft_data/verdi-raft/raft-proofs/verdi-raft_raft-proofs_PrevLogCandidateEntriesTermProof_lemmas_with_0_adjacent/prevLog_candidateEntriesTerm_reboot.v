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

Lemma prevLog_candidateEntriesTerm_reboot : refined_raft_net_invariant_reboot prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_reboot, prevLog_candidateEntriesTerm, reboot.
simpl.
intros.
eapply candidateEntriesTerm_ext; eauto.
repeat find_rewrite.
find_apply_hyp_hyp.
unfold candidateEntriesTerm in *.
break_exists_exists.
update_destruct_simplify; auto.
repeat find_rewrite.
simpl in *.
intuition.
discriminate.
