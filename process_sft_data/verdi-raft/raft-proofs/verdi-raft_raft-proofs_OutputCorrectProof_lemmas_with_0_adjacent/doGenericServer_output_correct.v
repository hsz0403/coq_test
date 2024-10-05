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

Lemma doGenericServer_output_correct : forall h ps sigma os st' ms, raft_intermediate_reachable (mkNetwork ps sigma) -> doGenericServer h (sigma h) = (os, st', ms) -> in_output_list client id out os -> output_correct client id out (applied_entries (update name_eq_dec sigma h st')).
Proof using lmi lacimi si smci.
intros.
find_copy_apply_lem_hyp logs_sorted_invariant.
pose proof entries_contiguous.
match goal with | H : context [contiguous_range_exact_lo] |- _ => specialize (H ({| nwPackets := ps; nwState := sigma |})) end.
concludes.
simpl in *.
find_copy_apply_lem_hyp state_machine_correct_invariant.
unfold state_machine_correct in *.
intuition.
unfold logs_sorted in *.
intuition.
unfold doGenericServer in *.
break_let.
find_inversion.
find_copy_apply_lem_hyp applyEntries_spec.
intuition.
repeat find_rewrite.
eapply applyEntries_output_correct with (es := rev (removeAfterIndex (log (sigma h)) (lastApplied (sigma h)))) in Heqp; eauto.
-
rewrite <- rev_app_distr in *.
eapply output_correct_prefix; eauto.
break_if.
+
do_bool.
erewrite findGtIndex_removeAfterIndex_i_lt_i' in *; eauto.
match goal with | |- context [applied_entries (update _ ?sigma ?h ?st)] => pose proof applied_entries_update sigma h st end.
conclude_using intuition.
intuition; simpl in *; unfold raft_data in *; simpl in *; find_rewrite; auto using Prefix_refl.
unfold applied_entries in *.
break_exists.
intuition.
repeat find_rewrite.
eapply contiguous_sorted_subset_prefix; eauto using removeAfterIndex_contiguous, removeAfterIndex_sorted.
intros.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
find_apply_lem_hyp removeAfterIndex_in.
apply removeAfterIndex_le_In; eauto; try omega.
find_copy_apply_lem_hyp commitIndex_lastApplied_match_invariant.
unfold commitIndex_lastApplied_match in *.
simpl in *.
match goal with | _ : ?x >= ?y |- _ => assert (y <= x) by omega end.
eapply_prop_hyp le le; eauto.
intuition.
+
do_bool.
erewrite findGtIndex_removeAfterIndex_i'_le_i in *; eauto.
match goal with | |- context [applied_entries (update _ ?sigma ?h ?st)] => pose proof applied_entries_update sigma h st end.
conclude_using intuition.
intuition; simpl in *; unfold raft_data in *; simpl in *; find_rewrite; auto using Prefix_refl.
unfold applied_entries in *.
break_exists.
intuition.
repeat find_rewrite.
eapply contiguous_sorted_subset_prefix; eauto using removeAfterIndex_contiguous, removeAfterIndex_sorted.
intros.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
find_apply_lem_hyp removeAfterIndex_in.
apply removeAfterIndex_le_In; eauto; try omega.
find_copy_apply_lem_hyp lastApplied_lastApplied_match_invariant.
unfold lastApplied_lastApplied_match in *.
simpl in *.
match goal with | _ : ?x >= ?y |- _ => assert (y <= x) by omega end.
eapply_prop_hyp le le; eauto.
intuition.
-
unfold client_cache_complete in *.
simpl in *.
intros.
subst.
find_apply_lem_hyp In_rev.
find_apply_hyp_hyp.
break_exists.
intuition.
repeat find_rewrite.
match goal with | H : Some _ = Some _ |- _ => invcs H end.
auto.
-
intros.
find_apply_lem_hyp In_rev.
eauto.
