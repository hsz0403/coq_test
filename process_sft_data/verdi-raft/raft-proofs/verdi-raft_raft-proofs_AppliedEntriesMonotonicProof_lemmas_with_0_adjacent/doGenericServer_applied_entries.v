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

Lemma doGenericServer_applied_entries : forall ps h sigma os st' ms, raft_intermediate_reachable (mkNetwork ps sigma) -> doGenericServer h (sigma h) = (os, st', ms) -> exists es, applied_entries (update name_eq_dec sigma h st') = (applied_entries sigma) ++ es.
Proof using lacimi si.
intros.
unfold doGenericServer in *.
break_let.
find_inversion.
use_applyEntries_spec.
subst.
simpl in *.
unfold raft_data in *.
simpl in *.
break_if; [|rewrite applied_entries_safe_update; simpl in *; eauto using app_nil_r].
do_bool.
match goal with | |- context [update _ ?sigma ?h ?st] => pose proof applied_entries_update sigma h st end.
simpl in *.
assert (commitIndex (sigma h) >= lastApplied (sigma h)) by omega.
concludes.
intuition.
-
find_rewrite.
eauto using app_nil_r.
-
pose proof applied_entries_cases sigma.
intuition; repeat find_rewrite; eauto.
match goal with | H : exists _, _ |- _ => destruct H as [h'] end.
repeat find_rewrite.
find_apply_lem_hyp argmax_elim.
intuition.
match goal with | H : forall _: name, _ |- _ => specialize (H h'); conclude H ltac:(eauto using all_fin_all) end.
rewrite_update.
simpl in *.
update_destruct_hyp; subst; rewrite_update; simpl in *.
+
apply rev_exists.
erewrite removeAfterIndex_le with (i := lastApplied (sigma h')) (j := commitIndex (sigma h')); [|omega].
eauto using removeAfterIndex_partition.
+
apply rev_exists.
match goal with | _ : ?h <> ?h' |- exists _, removeAfterIndex ?l (commitIndex (?sigma ?h)) = _ => pose proof removeAfterIndex_partition (removeAfterIndex l (commitIndex (sigma h))) (lastApplied (sigma h')) end.
break_exists_exists.
repeat match goal with | H : applied_entries _ = _ |- _ => clear H end.
find_rewrite.
f_equal.
erewrite <- removeAfterIndex_le; eauto.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
find_copy_apply_lem_hyp lastApplied_commitIndex_match_invariant.
eapply removeAfterIndex_same_sufficient; eauto; intros; eapply_prop_hyp lastApplied_commitIndex_match le; intuition eauto.
