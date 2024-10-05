Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.StateMachineCorrectInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.TraceUtil.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.OutputGreatestIdInterface.
Section OutputGreatestId.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lmi : log_matching_interface}.
Context {si : sorted_interface}.
Context {aemi : applied_entries_monotonic_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Context {smci : state_machine_correct_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Section inner.
Variable client : clientId.
Variables id id' : nat.
Variable id_lt_id' : id < id'.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := key_in_output_trace client id ; T_dec := key_in_output_trace_dec client id ; R := fun s => before_func (has_key client id) (has_key client id') (applied_entries (nwState (snd s))) }.
Next Obligation.
simpl in *.
find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
find_eapply_lem_hyp applied_entries_monotonic'; eauto.
break_exists; repeat find_rewrite.
eauto using before_func_app.
Defined.
Next Obligation.
unfold key_in_output_trace in *.
intuition.
break_exists; intuition.
Defined.
Next Obligation.
find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
find_apply_lem_hyp in_output_changed; auto.
eauto using output_implies_greatest.
Defined.
End inner.
Instance ogii : output_greatest_id_interface.
Proof.
split.
unfold greatest_id_for_client.
intros.
eauto using output_greatest_id.
End OutputGreatestId.

Lemma output_implies_greatest : forall failed net failed' net' o client id id', raft_intermediate_reachable net -> @step_failure _ _ failure_params (failed, net) (failed', net') o -> key_in_output_trace client id o -> id < id' -> before_func (has_key client id) (has_key client id') (applied_entries (nwState net')).
Proof using lacimi smci si lmi.
intros.
invcs H0; simpl in *; try match goal with | _ : key_in_output_trace _ _ [] |- _ => unfold key_in_output_trace in *; break_exists; simpl in *; intuition end.
-
unfold key_in_output_trace in *.
break_exists; simpl in *; intuition.
find_inversion.
unfold RaftNetHandler in *.
repeat break_let.
repeat find_inversion.
simpl in *.
find_eapply_lem_hyp RIR_handleMessage; eauto.
find_copy_eapply_lem_hyp RIR_doLeader; simpl in *; rewrite_update; eauto.
find_apply_lem_hyp key_in_output_list_split.
intuition; [exfalso; eapply doLeader_key_in_output_list; eauto|].
match goal with | _ : doLeader ?st ?h = _, _ : doGenericServer _ ?d = _ |- _ => replace st with ((update name_eq_dec (nwState net) h st) h) in *; [|rewrite_update; auto] end.
find_apply_lem_hyp doLeader_appliedEntries.
rewrite_update.
repeat find_rewrite_lem update_overwrite.
unfold data in *.
simpl in *.
match goal with | _ : raft_intermediate_reachable (mkNetwork ?ps ?st), H : doGenericServer ?h ?r = _ |- _ => replace r with (nwState (mkNetwork ps st) h) in H by (simpl in *; rewrite_update; auto) end.
find_eapply_lem_hyp doGenericServer_key_in_output_list; [|idtac|eauto|]; eauto.
simpl in *.
find_rewrite_lem update_overwrite.
auto.
-
unfold key_in_output_trace in *.
break_exists; simpl in *; intuition.
find_inversion.
unfold RaftInputHandler in *.
repeat break_let.
repeat find_inversion.
simpl in *.
find_copy_eapply_lem_hyp RIR_handleInput; eauto.
find_copy_eapply_lem_hyp RIR_doLeader; simpl in *; rewrite_update; eauto.
find_apply_lem_hyp key_in_output_list_split.
intuition; [exfalso; eapply handleInput_key_in_output_list; eauto|].
find_apply_lem_hyp key_in_output_list_split.
intuition; [exfalso; eapply doLeader_key_in_output_list; eauto|].
match goal with | _ : doLeader ?st ?h = _, _ : doGenericServer _ ?d = _ |- _ => replace st with ((update name_eq_dec (nwState net) h st) h) in *; [|rewrite_update; auto] end.
find_apply_lem_hyp doLeader_appliedEntries.
rewrite_update.
repeat find_rewrite_lem update_overwrite.
unfold data in *.
simpl in *.
match goal with | _ : raft_intermediate_reachable (mkNetwork ?ps ?st), H : doGenericServer ?h ?r = _ |- _ => replace r with (nwState (mkNetwork ps st) h) in H by (simpl in *; rewrite_update; auto) end.
find_eapply_lem_hyp doGenericServer_key_in_output_list; [|idtac|eauto|]; eauto.
simpl in *.
find_rewrite_lem update_overwrite.
auto.
