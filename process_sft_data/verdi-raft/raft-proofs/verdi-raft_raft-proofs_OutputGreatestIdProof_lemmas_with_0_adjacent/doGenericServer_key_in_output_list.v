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

Lemma doGenericServer_key_in_output_list : forall net h os st' ms id' client id, raft_intermediate_reachable net -> doGenericServer h (nwState net h) = (os, st', ms) -> key_in_output_list client id os -> id < id' -> before_func (has_key client id) (has_key client id') (applied_entries (update name_eq_dec (nwState net) h st')).
Proof using lacimi smci si lmi.
intros.
find_copy_apply_lem_hyp logs_sorted_invariant.
pose proof entries_contiguous.
match goal with | H : context [contiguous_range_exact_lo] |- _ => specialize (H net) end.
concludes.
simpl in *.
find_copy_apply_lem_hyp state_machine_correct_invariant.
unfold state_machine_correct in *.
intuition.
unfold logs_sorted in *.
intuition.
unfold key_in_output_list in *.
match goal with | H : exists _, _ |- _ => destruct H as [o] end.
unfold doGenericServer in *.
break_let.
simpl in *.
find_inversion.
simpl in *.
pose proof Heqp as Heqp'.
eapply applyEntries_before in Heqp; eauto.
match goal with | H : before_func _ _ ?l |- _=> eapply before_func_prepend with (l' := (rev (removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h))))) in H end; eauto; [|intros; find_apply_lem_hyp In_rev; apply Bool.not_true_iff_false; intuition; unfold has_key in *; break_match; break_if; repeat (do_bool; intuition); simpl in *; eapply_prop_hyp client_cache_complete In; eauto; break_exists; intuition; simpl in *; subst; match goal with | Ha : context [applyEntries], Hg : getLastId _ _ = Some (?x, _) |- _ => eapply applyEntries_cache with (id' := x) in Ha end; eauto; omega; intuition; find_rewrite; repeat find_rewrite].
rewrite <- rev_app_distr in *.
eapply before_func_prefix; eauto.
use_applyEntries_spec.
subst.
simpl in *.
break_if.
-
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
-
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
