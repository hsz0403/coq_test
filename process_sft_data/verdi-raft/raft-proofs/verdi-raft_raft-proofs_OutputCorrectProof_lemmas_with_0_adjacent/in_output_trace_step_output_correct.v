Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.OutputCorrectInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.StateMachineCorrectInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.LogMatchingInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section OutputCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aemi : applied_entries_monotonic_interface}.
Context {smci : state_machine_correct_interface}.
Context {si : sorted_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Context {lmi : log_matching_interface}.
Section inner.
Variable client : clientId.
Variables id : nat.
Variable out : output.
Ltac intermediate_networks := match goal with | Hdgs : doGenericServer ?h ?st' = _, Hdl : doLeader ?st ?h = _ |- context [update _ (nwState ?net) ?h ?st''] => replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq; replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq; let H := fresh "H" in assert (update name_eq_dec (nwState net) h st'' = update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H end.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := in_output_trace client id out ; T_dec := in_output_trace_dec ; R := fun s => let (_, net) := s in output_correct client id out (applied_entries (nwState net)) }.
Next Obligation.
repeat break_let.
subst.
find_eapply_lem_hyp applied_entries_monotonic'; eauto using step_failure_star_raft_intermediate_reachable.
unfold output_correct in *.
break_exists.
repeat find_rewrite.
match goal with | [ |- context [ deduplicate_log (?l ++ ?l') ] ] => pose proof deduplicate_log_app l l'; break_exists; find_rewrite end.
repeat eexists; intuition eauto; repeat find_rewrite; auto.
rewrite app_ass.
simpl.
repeat f_equal.
Defined.
Next Obligation.
unfold in_output_trace in *.
intuition.
break_exists; intuition.
Defined.
Next Obligation.
find_apply_lem_hyp in_output_changed; auto.
eauto using in_output_trace_step_output_correct, step_failure_star_raft_intermediate_reachable.
Defined.
End inner.
Instance oci : output_correct_interface.
Proof using smci si lmi lacimi aemi.
split.
exact output_correct.
End OutputCorrect.

Lemma in_output_trace_step_output_correct : forall failed failed' (net net' : network (params := @multi_params _ _ raft_params)) os, in_output_trace client id out os -> @raft_intermediate_reachable _ _ raft_params net -> step_failure (failed, net) (failed', net') os -> output_correct client id out (applied_entries (nwState net')).
Proof using lmi lacimi si smci.
intros.
match goal with | [ H : context [ step_failure _ _ _ ] |- _ ] => invcs H end.
-
unfold RaftNetHandler in *.
repeat break_let.
repeat find_inversion.
find_apply_lem_hyp in_output_trace_singleton_inv.
find_apply_lem_hyp in_output_list_app_or.
intuition.
+
exfalso.
eapply doLeader_key_in_output_list; eauto.
+
find_copy_eapply_lem_hyp RIR_handleMessage; eauto.
find_copy_eapply_lem_hyp RIR_doLeader; simpl; rewrite_update; eauto.
intermediate_networks.
find_copy_apply_lem_hyp doLeader_appliedEntries.
eapply doGenericServer_output_correct; eauto.
-
unfold RaftInputHandler in *.
repeat break_let.
repeat find_inversion.
find_apply_lem_hyp in_output_trace_inp_inv.
find_apply_lem_hyp in_output_trace_singleton_inv.
find_apply_lem_hyp in_output_list_app_or.
intuition.
+
exfalso.
eapply handleInput_in_output_list; eauto.
+
find_apply_lem_hyp in_output_list_app_or.
intuition.
*
exfalso.
eapply doLeader_key_in_output_list; eauto.
*
find_copy_eapply_lem_hyp RIR_handleInput; eauto.
find_copy_eapply_lem_hyp RIR_doLeader; simpl; rewrite_update; eauto.
intermediate_networks.
find_copy_apply_lem_hyp doLeader_appliedEntries.
eapply doGenericServer_output_correct; eauto.
-
exfalso.
eauto using in_output_trace_not_nil.
-
exfalso.
eauto using in_output_trace_not_nil.
-
exfalso.
eauto using in_output_trace_not_nil.
-
exfalso.
eauto using in_output_trace_not_nil.
