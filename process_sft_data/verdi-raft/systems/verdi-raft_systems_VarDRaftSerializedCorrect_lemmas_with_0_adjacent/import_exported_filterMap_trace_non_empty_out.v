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

Lemma import_exported_filterMap_trace_non_empty_out : forall tr, import tr = import (filterMap trace_non_empty_out tr).
Proof using.
induction tr; simpl; auto.
destruct a, s; simpl.
-
rewrite IHtr; auto.
-
rewrite IHtr.
destruct l; auto.
