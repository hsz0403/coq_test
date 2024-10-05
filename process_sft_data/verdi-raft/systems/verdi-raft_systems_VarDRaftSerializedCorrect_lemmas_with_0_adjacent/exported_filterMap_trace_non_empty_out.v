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

Lemma exported_filterMap_trace_non_empty_out : forall tr tr' l tr1, exported (get_input tr') (get_output tr') l tr1 -> filterMap trace_non_empty_out tr = filterMap trace_non_empty_out tr' -> exported (get_input tr) (get_output tr) l tr1.
Proof using.
intros tr tr' l tr1 H_exp H_eq.
rewrite get_input_tr_filterMap_trace_non_empty_out in H_exp.
rewrite get_output_tr_filterMap_trace_non_empty_out in H_exp.
rewrite <- H_eq in H_exp.
rewrite <- get_input_tr_filterMap_trace_non_empty_out in H_exp.
rewrite <- get_output_tr_filterMap_trace_non_empty_out in H_exp.
auto.
