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

Theorem applied_entries_monotonic' : forall failed net failed' net' os, raft_intermediate_reachable net -> (@step_failure _ _ failure_params (failed, net) (failed', net') os) -> exists es, applied_entries (nwState net') = applied_entries (nwState net) ++ es.
Proof using lacimi misi smsi uii lmi si.
intros.
match goal with H : step_failure _ _ _ |- _ => invcs H end.
-
unfold RaftNetHandler in *.
repeat break_let.
subst.
find_inversion.
match goal with | Hdl : doLeader ?st ?h = _, Hdgs : doGenericServer ?h ?st' = _ |- context [update _ (nwState ?net) ?h ?st''] => replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq; replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq; let H := fresh "H" in assert (update name_eq_dec (nwState net) h st'' = update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H end.
find_copy_apply_lem_hyp doLeader_appliedEntries.
find_copy_eapply_lem_hyp RIR_handleMessage; eauto.
find_eapply_lem_hyp RIR_doLeader; simpl in *; eauto.
find_apply_lem_hyp handleMessage_applied_entries; auto; [|destruct p; find_rewrite; in_crush].
unfold raft_data in *.
simpl in *.
unfold raft_data in *.
simpl in *.
match goal with | H : applied_entries (update _ (update _ _ _ _) _ _) = applied_entries (update _ _ _ _) |- _ => symmetry in H end.
repeat find_rewrite.
repeat match goal with H : applied_entries _ = applied_entries _ |- _ => clear H end.
eauto using doGenericServer_applied_entries.
-
unfold RaftInputHandler in *.
repeat break_let.
subst.
find_inversion.
match goal with | Hdgs : doGenericServer ?h ?st' = _, Hdl : doLeader ?st ?h = _ |- context [update _ (nwState ?net) ?h ?st''] => replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq; replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq; let H := fresh "H" in assert (update name_eq_dec (nwState net) h st'' = update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H end.
find_copy_apply_lem_hyp doLeader_appliedEntries.
find_copy_eapply_lem_hyp RIR_handleInput; eauto.
find_eapply_lem_hyp RIR_doLeader; simpl in *; eauto.
find_apply_lem_hyp handleInput_applied_entries; auto.
unfold raft_data in *.
simpl in *.
unfold raft_data in *.
simpl in *.
match goal with | H : applied_entries (update _ (update _ _ _ _) _ _) = applied_entries (update _ _ _ _) |- _ => symmetry in H end.
repeat find_rewrite.
repeat match goal with H : applied_entries _ = applied_entries _ |- _ => clear H end.
eauto using doGenericServer_applied_entries.
-
exists nil; intuition.
-
exists nil; intuition.
-
exists nil; intuition.
-
exists nil.
rewrite app_nil_r.
apply applied_entries_log_lastApplied_same; intros; unfold reboot in *; update_destruct_max_simplify; auto.
