Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.AllEntriesIndicesGt0Interface.
Section AllEntriesIndicesGt0.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Instance aeigt0 : allEntries_indices_gt_0_interface.
Proof.
constructor.
exact allEntries_indices_gt_0_invariant.
End AllEntriesIndicesGt0.

Lemma lifted_taifol_nw : forall net, refined_raft_intermediate_reachable net -> forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit, In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> terms_and_indices_from_one entries.
Proof using taifoli rri.
intros.
pose proof (lift_prop _ terms_and_indices_from_one_log_nw_invariant).
match goal with | [ H : _ |- _ ] => eapply H; eauto using ghost_packet end.
