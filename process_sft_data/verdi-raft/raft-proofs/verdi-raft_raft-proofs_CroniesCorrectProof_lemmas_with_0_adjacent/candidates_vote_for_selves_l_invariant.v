Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section CroniesCorrectProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cvfsi : candidates_vote_for_selves_interface}.
Instance cci : cronies_correct_interface.
Proof.
split.
auto using cronies_correct_invariant.
End CroniesCorrectProof.

Lemma candidates_vote_for_selves_l_invariant : forall (net : network), refined_raft_intermediate_reachable net -> candidates_vote_for_selves (deghost net).
Proof using cvfsi rri.
intros.
eapply lift_prop; [exact candidates_vote_for_selves_invariant|eauto].
