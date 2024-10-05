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

Lemma doGenericServer_applied_entries : forall ps h sigma os st' ms, raft_intermediate_reachable (mkNetwork ps sigma) -> doGenericServer h (sigma h) = (os, st', ms) -> exists es, applied_entries (update name_eq_dec sigma h st') = (applied_entries sigma) ++ es /\ (forall e, In e es -> exists h, In e (log (sigma h)) /\ eIndex e <= commitIndex (sigma h)).
Proof using lacimi si.
intros.
unfold doGenericServer in *.
break_let.
find_inversion.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted, logs_sorted_host in *.
intuition.
use_applyEntries_spec.
subst.
simpl in *.
unfold raft_data in *.
simpl in *.
break_if; [|rewrite applied_entries_safe_update; simpl in *; eauto; exists nil; simpl in *; intuition].
do_bool.
match goal with | |- context [update _ ?sigma ?h ?st] => pose proof applied_entries_update sigma h st end.
simpl in *.
assert (commitIndex (sigma h) >= lastApplied (sigma h)) by omega.
concludes.
intuition; [find_rewrite; exists nil; simpl in *; intuition|].
pose proof applied_entries_cases sigma.
intuition; repeat find_rewrite; eauto; [eexists; intuition; eauto; find_apply_lem_hyp in_rev; find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto; find_apply_lem_hyp removeAfterIndex_in; eexists; intuition; eauto|].
match goal with | H : exists _, _ |- _ => destruct H as [h'] end.
repeat find_rewrite.
find_apply_lem_hyp argmax_elim.
intuition.
match goal with | H : forall _: name, _ |- _ => specialize (H h'); conclude H ltac:(eauto using all_fin_all) end.
rewrite_update.
simpl in *.
update_destruct; subst; rewrite_update; simpl in *.
+
match goal with | h : name |- _ => pose proof removeAfterIndex_partition (removeAfterIndex (log (sigma h)) (commitIndex (sigma h))) (lastApplied (sigma h)) end.
find_apply_lem_hyp rev_exists.
break_exists_exists.
repeat find_rewrite.
rewrite <- removeAfterIndex_le by omega.
intuition.
find_eapply_lem_hyp app_in_2; eauto.
find_apply_lem_hyp In_rev.
find_copy_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp removeAfterIndex_In_le; eauto.
+
match goal with | _ : ?h <> ?h' |- context [ removeAfterIndex ?l (commitIndex (?sigma ?h)) ] => pose proof removeAfterIndex_partition (removeAfterIndex l (commitIndex (sigma h))) (lastApplied (sigma h')) end.
find_apply_lem_hyp rev_exists.
break_exists_exists.
repeat match goal with | H : applied_entries _ = _ |- _ => clear H end.
find_rewrite.
erewrite <- removeAfterIndex_le; eauto.
intuition.
*
f_equal.
f_equal.
find_copy_apply_lem_hyp lastApplied_commitIndex_match_invariant.
eapply removeAfterIndex_same_sufficient; eauto; intros; eapply_prop_hyp lastApplied_commitIndex_match le; intuition eauto.
*
find_eapply_lem_hyp app_in_2; eauto.
find_apply_lem_hyp In_rev.
find_copy_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp removeAfterIndex_In_le; eauto.
