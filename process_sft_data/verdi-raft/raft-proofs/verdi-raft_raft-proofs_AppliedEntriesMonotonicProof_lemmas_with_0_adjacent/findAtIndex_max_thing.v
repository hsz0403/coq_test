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

Lemma findAtIndex_max_thing : forall net h e i, raft_intermediate_reachable net -> In e (log (nwState net h)) -> eIndex e > i -> 1 <= i -> exists e', findAtIndex (log (nwState net h)) i = Some e'.
Proof using lmi si.
intros.
find_copy_apply_lem_hyp logs_sorted_invariant.
pose proof log_matching_invariant.
eapply_prop_hyp raft_intermediate_reachable raft_intermediate_reachable.
unfold log_matching, log_matching_hosts, logs_sorted in *.
intuition.
match goal with | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h i); conclude H ltac:(intuition; find_apply_lem_hyp maxIndex_is_max; eauto; omega) end.
break_exists_exists.
intuition.
apply findAtIndex_intro; eauto using sorted_uniqueIndices.
