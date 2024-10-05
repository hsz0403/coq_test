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

Lemma entries_max_thing : forall net p es, raft_intermediate_reachable net -> In p (nwPackets net) -> mEntries (pBody p) = Some es -> es <> nil -> 1 <= maxIndex es.
Proof using lmi.
intros.
find_apply_lem_hyp maxIndex_non_empty.
break_exists; intuition; find_rewrite.
find_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_nw in *.
intuition.
destruct (pBody p) eqn:?; simpl in *; try congruence.
find_apply_hyp_hyp.
intuition.
find_inversion.
find_apply_hyp_hyp.
omega.
