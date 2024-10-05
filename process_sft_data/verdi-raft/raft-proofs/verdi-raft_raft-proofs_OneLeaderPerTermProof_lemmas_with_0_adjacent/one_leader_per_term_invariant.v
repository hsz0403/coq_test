Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Section OneLeaderPerTermProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Ltac copy_eapply_prop_hyp P H := match goal with | H' : P _ |- _ => let x := fresh in pose proof H as x; apply H' in x end.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Instance olpti : one_leader_per_term_interface.
Proof.
split.
auto using one_leader_per_term_invariant.
End OneLeaderPerTermProof.

Theorem one_leader_per_term_invariant : forall net, raft_intermediate_reachable net -> one_leader_per_term net.
Proof using cci vci rri.
intros.
apply lower_prop; auto.
intros.
apply one_leader_per_term_invariant'.
-
eauto using votes_correct_invariant.
-
eauto using cronies_correct_invariant.
