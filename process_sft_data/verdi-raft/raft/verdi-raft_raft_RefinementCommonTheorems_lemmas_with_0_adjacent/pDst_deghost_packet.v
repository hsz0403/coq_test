Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CommonTheorems.
Require Export VerdiRaft.RefinementCommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section CommonTheorems.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {cci : cronies_correct_interface}.
Context {vci : votes_correct_interface}.
End CommonTheorems.
Ltac intro_refined_invariant lem := match goal with | [ h: refined_raft_intermediate_reachable _ |- _ ] => let x := fresh in pose proof h as x; apply lem in x; unfold_invariant x end.

Lemma pDst_deghost_packet : forall p : packet (params := raft_refined_multi_params), pDst (deghost_packet p) = pDst p.
Proof using.
unfold deghost_packet.
auto.
