Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.TraceUtil.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Section OutputImpliesApplied.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lmi : log_matching_interface}.
Context {si : sorted_interface}.
Context {aemi : applied_entries_monotonic_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := key_in_output_trace client id ; T_dec := key_in_output_trace_dec client id ; R := fun s => in_applied_entries client id (snd s) }.
Next Obligation.
unfold in_applied_entries in *.
break_exists; eexists; intuition eauto.
eapply applied_entries_monotonic; eauto.
eauto using refl_trans_1n_n1_trace, step_failure_star_raft_intermediate_reachable.
Defined.
Next Obligation.
unfold key_in_output_trace in *.
intuition.
break_exists; intuition.
Defined.
Next Obligation.
simpl in *.
find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
find_apply_lem_hyp in_output_changed; auto.
eauto using output_implies_in_applied_entries.
Defined.
End inner.
Instance oiai : output_implies_applied_interface.
Proof.
split.
intros.
eapply output_implies_applied; eauto.
End OutputImpliesApplied.

Lemma output_implies_in_applied_entries : forall failed net failed' net' o, raft_intermediate_reachable net -> @step_failure _ _ failure_params (failed, net) (failed', net') o -> key_in_output_trace client id o -> in_applied_entries client id net'.
Proof using misi smsi lmi.
intros.
invcs H0; simpl in *; try match goal with | _ : key_in_output_trace _ _ [] |- _ => unfold key_in_output_trace in *; break_exists; simpl in *; intuition end.
-
unfold key_in_output_trace in *.
break_exists; simpl in *; intuition.
find_inversion.
unfold in_applied_entries in *.
simpl in *.
unfold RaftNetHandler in *.
repeat break_let.
repeat find_inversion.
simpl in *.
find_eapply_lem_hyp RIR_handleMessage; eauto.
find_apply_lem_hyp key_in_output_list_split.
find_copy_apply_lem_hyp doLeader_key_in_output_list.
intuition.
match goal with | H : doLeader ?st ?h = _ |- _ => replace st with ((update name_eq_dec (nwState net) h st) h) in H; [|rewrite_update; auto] end.
find_eapply_lem_hyp RIR_doLeader; eauto.
simpl in *.
match goal with | _ : raft_intermediate_reachable ?net' |- context [update _ (nwState net) ?h ?d] => remember net' as n; assert ((update name_eq_dec (nwState net) h d) = (update name_eq_dec (nwState n) h d)) by (subst; simpl in *; repeat rewrite update_overwrite; auto) end.
unfold raft_data in *.
simpl in *.
unfold raft_data in *.
simpl in *.
repeat find_rewrite.
eapply doGenericServer_key_in_output_list; eauto.
simpl in *.
rewrite_update; eauto.
-
unfold key_in_output_trace in *.
break_exists; simpl in *; intuition.
find_inversion.
unfold in_applied_entries in *.
simpl in *.
unfold RaftInputHandler in *.
repeat break_let.
repeat find_inversion.
simpl in *.
find_copy_eapply_lem_hyp RIR_handleInput; eauto.
find_apply_lem_hyp key_in_output_list_split.
intuition; [exfalso; eapply handleInput_key_in_output_list; eauto|].
find_apply_lem_hyp key_in_output_list_split.
intuition; [exfalso; eapply doLeader_key_in_output_list; eauto|].
match goal with | H : doLeader ?st ?h = _ |- _ => replace st with ((update name_eq_dec (nwState net) h st) h) in H; [|rewrite_update; auto] end.
find_eapply_lem_hyp RIR_doLeader; eauto.
simpl in *.
match goal with | _ : raft_intermediate_reachable ?net' |- context [update _ (nwState net) ?h ?d] => remember net' as n; assert ((update name_eq_dec (nwState net) h d) = (update name_eq_dec (nwState n) h d)) by (subst; simpl in *; repeat rewrite update_overwrite; auto) end.
unfold raft_data in *.
simpl in *.
unfold raft_data in *.
simpl in *.
repeat find_rewrite.
eapply doGenericServer_key_in_output_list; eauto.
simpl in *.
rewrite_update; eauto.
