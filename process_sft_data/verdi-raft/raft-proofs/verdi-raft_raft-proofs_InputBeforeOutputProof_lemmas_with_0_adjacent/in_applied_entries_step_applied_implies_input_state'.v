Require Import Verdi.GhostSimulations.
Require Import Verdi.InverseTraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.InputBeforeOutputInterface.
Require Import VerdiRaft.AppliedImpliesInputInterface.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.UniqueIndicesInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section InputBeforeOutput.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {oiai : output_implies_applied_interface}.
Context {aiii : applied_implies_input_interface}.
Context {si : sorted_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Context {lmi : log_matching_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Context {uii : unique_indices_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Fixpoint client_id_in l := match l with | [] => false | e :: l' => if (andb (if clientId_eq_dec (eClient e) client then true else false) (eId e =? id)) then true else client_id_in l' end.
Program Instance TR : InverseTraceRelation step_failure := { init := step_failure_init; T := input_before_output client id; R := fun s => in_applied_entries client id (snd s) }.
Next Obligation.
destruct (client_id_in (applied_entries (nwState n))) eqn:?; eauto using client_id_in_true_in_applied_entries, client_id_in_false_not_in_applied_entries.
Defined.
Next Obligation.
unfold input_before_output in *.
eauto using before_func_app.
Defined.
Next Obligation.
intuition.
simpl in *.
unfold in_applied_entries, applied_entries in *.
simpl in *.
break_match; simpl in *; break_exists; intuition.
Defined.
Next Obligation.
simpl in *.
find_eapply_lem_hyp in_applied_entries_step_applied_implies_input_state; eauto.
break_or_hyp.
-
break_exists.
intuition.
find_eapply_lem_hyp applied_implies_input; eauto.
apply before_func_app.
destruct (key_in_output_trace_dec client id tr); [find_eapply_lem_hyp output_implies_applied; eauto; intuition|].
fold (input_before_output client id tr).
subst.
eauto using in_input_not_in_output_input_before_output.
-
destruct (key_in_output_trace_dec client id tr); [find_eapply_lem_hyp output_implies_applied; eauto; intuition|].
break_exists.
subst.
eauto using input_before_output_not_key_in_output_trace_snoc_key.
Defined.
End inner.
Instance iboi : input_before_output_interface.
Proof.
split.
intros.
eapply output_implies_input_before_output; eauto.
End InputBeforeOutput.

Lemma in_applied_entries_step_applied_implies_input_state' : forall (failed : list name) net failed' net' o, raft_intermediate_reachable net -> step_failure (failed, net) (failed', net') o -> ~ in_applied_entries client id net -> in_applied_entries client id net' -> (exists e, eClient e = client /\ eId e = id /\ applied_implies_input_state client id (eInput e) net) \/ exists h o' inp, o = (h, inl (ClientRequest client id inp)) :: o'.
Proof using uii misi smsi lmi lacimi si.
intros.
match goal with H : step_failure _ _ _ |- _ => invcs H end; intuition.
-
left.
unfold RaftNetHandler in *.
repeat break_let.
subst.
unfold in_applied_entries in *.
break_exists_exists.
intuition.
find_inversion.
match goal with | Hdgs : doGenericServer ?h ?st' = _, Hdl : doLeader ?st ?h = _, _ :context [update _ (nwState ?net) ?h ?st''] |- _ => replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq; replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq; let H := fresh "H" in assert (update name_eq_dec (nwState net) h st'' = update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') as H by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H in *; clear H end.
find_copy_eapply_lem_hyp RIR_handleMessage; eauto.
find_eapply_lem_hyp RIR_doLeader; simpl in *; eauto.
simpl in *.
find_copy_apply_lem_hyp handleMessage_applied_entries; repeat find_rewrite; eauto; try solve [destruct p; simpl in *; intuition].
find_copy_apply_lem_hyp doLeader_appliedEntries.
find_eapply_lem_hyp doGenericServer_applied_entries; eauto.
break_exists.
intuition.
unfold ghost_data in *.
simpl in *.
repeat find_rewrite.
do_in_app.
intuition.
+
contradict H1.
eexists; intuition; repeat find_rewrite; eauto.
+
find_apply_hyp_hyp.
break_exists.
intuition.
eapply handleMessage_log with (h'' := x1); eauto; [destruct p; simpl in *; repeat find_rewrite; intuition|].
update_destruct; subst; rewrite_update; eauto.
find_apply_lem_hyp doLeader_log.
repeat find_rewrite.
auto.
-
unfold RaftInputHandler in *.
repeat break_let.
subst.
unfold in_applied_entries in *.
break_exists_exists.
intuition.
find_inversion.
match goal with | Hdgs : doGenericServer ?h ?st' = _, Hdl : doLeader ?st ?h = _, _ :context [update _ (nwState ?net) ?h ?st''] |- _ => replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq; replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq; let H := fresh "H" in assert (update name_eq_dec (nwState net) h st'' = update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') as H by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H in *; clear H end.
find_copy_eapply_lem_hyp RIR_handleInput; eauto.
find_eapply_lem_hyp RIR_doLeader; simpl in *; eauto.
simpl in *.
find_copy_apply_lem_hyp handleInput_applied_entries; repeat find_rewrite; eauto; try solve [destruct p; simpl in *; intuition].
find_copy_apply_lem_hyp doLeader_appliedEntries.
find_eapply_lem_hyp doGenericServer_applied_entries; eauto.
break_exists.
intuition.
unfold ghost_data in *.
simpl in *.
repeat find_rewrite.
match goal with | H : In _ _ -> False |- _ => clear H end.
do_in_app.
intuition.
+
find_false.
eexists; intuition; repeat find_rewrite; eauto.
+
find_apply_hyp_hyp.
break_exists.
intuition.
find_apply_lem_hyp doLeader_log.
match goal with | H : _ |- _ => eapply handleInput_log with (h' := x1) in H end; eauto; [|update_destruct; subst; eauto; rewrite_update; repeat find_rewrite; eauto].
intuition; subst; repeat find_rewrite; eauto.
-
find_false.
unfold in_applied_entries in *.
break_exists_exists.
intuition.
match goal with | H : In _ (applied_entries _) |- In _ (applied_entries ?sig) => erewrite applied_entries_log_lastApplied_same with (sigma := sig) in H end; auto; intros; simpl in *; update_destruct_max_simplify; auto.
