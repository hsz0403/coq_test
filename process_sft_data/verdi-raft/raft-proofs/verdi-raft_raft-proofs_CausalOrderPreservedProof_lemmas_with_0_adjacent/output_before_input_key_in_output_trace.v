Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.CausalOrderPreservedInterface.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Require Import VerdiRaft.AppliedImpliesInputInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Section CausalOrderPreserved.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {oiai : output_implies_applied_interface}.
Context {aiii : applied_implies_input_interface}.
Context {aemi : applied_entries_monotonic_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Variable client' : clientId.
Variable id' : nat.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := output_before_input client id client' id'; R := fun s => entries_ordered client id client' id' (snd s) }.
Next Obligation.
unfold output_before_input.
eapply before_func_dec.
Defined.
Next Obligation.
simpl in *.
unfold entries_ordered in *.
find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
find_eapply_lem_hyp applied_entries_monotonic'; eauto.
break_exists; repeat find_rewrite.
eauto using before_func_app.
Defined.
Next Obligation.
simpl in *.
find_copy_eapply_lem_hyp output_before_input_not_key_in_input_trace; eauto.
find_copy_apply_lem_hyp output_before_input_key_in_output_trace.
find_eapply_lem_hyp output_implies_applied; [|eapply refl_trans_n1_1n_trace; econstructor; eauto using refl_trans_1n_n1_trace].
eapply in_applied_entries_entries_ordered; auto.
intuition.
find_false.
find_apply_lem_hyp in_applied_entries_applied_implies_input_state.
break_exists.
intuition.
eexists.
eapply applied_implies_input; eauto.
eapply refl_trans_n1_1n_trace; econstructor; eauto using refl_trans_1n_n1_trace.
Defined.
End inner.
Instance copi : causal_order_preserved_interface.
Proof.
split.
intros.
eapply causal_order_preserved; eauto.
End CausalOrderPreserved.

Lemma output_before_input_key_in_output_trace : forall tr, output_before_input client id client' id' tr -> key_in_output_trace client id tr.
Proof using.
intros.
unfold output_before_input in *.
induction tr; simpl in *; intuition.
-
unfold key_in_output_trace.
unfold is_output_with_key in *.
repeat break_match; try congruence.
subst.
do 2 eexists.
intuition; eauto.
-
unfold key_in_output_trace in *.
break_exists_exists.
simpl; intuition.
