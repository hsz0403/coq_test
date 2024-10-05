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

Lemma handleInput_applied_entries : forall net h inp os st' ms, raft_intermediate_reachable net -> handleInput h inp (nwState net h) = (os, st', ms) -> applied_entries (nwState net) = applied_entries (update name_eq_dec (nwState net) h st').
Proof using misi.
intros.
symmetry.
unfold handleInput in *.
break_match; repeat break_let; repeat find_inversion.
-
apply applied_entries_log_lastApplied_update_same; eauto using handleTimeout_log, handleTimeout_lastApplied.
-
apply applied_entries_safe_update; eauto using handleClientRequest_lastApplied.
destruct (log st') using (handleClientRequest_log_ind ltac:(eauto)); auto.
simpl in *.
break_if; auto.
exfalso.
do_bool.
find_apply_lem_hyp max_index_sanity_invariant.
unfold maxIndex_sanity, maxIndex_lastApplied in *.
intuition.
match goal with | H : forall _, _ |- _ => specialize (H h) end.
omega.
