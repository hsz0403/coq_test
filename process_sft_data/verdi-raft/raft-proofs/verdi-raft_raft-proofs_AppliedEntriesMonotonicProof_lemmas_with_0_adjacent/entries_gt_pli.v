Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.UniqueIndicesInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.CommitRecordedCommittedInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Section AppliedEntriesMonotonicProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {uii : unique_indices_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Context {crci : commit_recorded_committed_interface}.
Context {lci : leader_completeness_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Instance aemi : applied_entries_monotonic_interface.
Proof.
split; eauto using applied_entries_monotonic, applied_entries_monotonic'.
End AppliedEntriesMonotonicProof.

Lemma entries_gt_pli : forall net p e t n pli plt es ci, raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In e es -> pli < eIndex e.
Proof using lmi.
intros.
find_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_nw in *.
intuition.
destruct (pBody p) eqn:?; simpl in *; try congruence.
find_inversion.
find_apply_hyp_hyp.
intuition.
