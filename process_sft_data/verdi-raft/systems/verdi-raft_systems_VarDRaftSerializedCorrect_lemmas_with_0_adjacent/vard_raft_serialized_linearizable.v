Require Import Verdi.Verdi.
Require Import Verdi.VarD.
Require Import Verdi.PartialMapSimulations.
Require Import Cheerios.Cheerios.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.Linearizability.
Require Import VerdiRaft.RaftLinearizableProofs.
Require Import VerdiRaft.EndToEndLinearizability.
Require Import Verdi.SerializedMsgParamsCorrect.
Require Import VerdiRaft.VarDRaftSerialized.
Section VarDSerializedCorrect.
Variable n : nat.
Instance raft_params : RaftParams VarD.vard_base_params := raft_params n.
Instance base_params : BaseParams := transformed_base_params n.
Instance multi_params : MultiParams _ := transformed_multi_params n.
Instance failure_params : FailureParams _ := transformed_failure_params n.
End VarDSerializedCorrect.

Theorem vard_raft_serialized_linearizable : forall failed net tr, input_correct tr -> step_failure_star step_failure_init (failed, net) tr -> exists l tr1 st, equivalent _ (import tr) l /\ exported (get_input tr) (get_output tr) l tr1 /\ step_1_star init st tr1.
Proof using.
intros failed net tr H_inp H_step.
apply step_failure_deserialized_simulation_star in H_step.
break_exists_name tr'.
break_and.
find_apply_lem_hyp raft_linearizable.
-
break_exists_name l.
break_exists_name tr1.
break_exists_name st.
break_and.
exists l, tr1, st.
split.
*
eapply equivalent_filterMap_trace_non_empty_out; eauto.
*
split; auto.
eapply exported_filterMap_trace_non_empty_out; eauto.
-
eapply input_correct_filterMap_trace_non_empty_out; eauto.
