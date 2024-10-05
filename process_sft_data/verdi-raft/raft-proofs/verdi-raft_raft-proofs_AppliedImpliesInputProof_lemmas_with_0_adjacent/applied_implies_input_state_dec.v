Require Import Verdi.InverseTraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppliedImpliesInputInterface.
Section AppliedImpliesInputProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {oiai : output_implies_applied_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Variable i : input.
Definition aiis_host (net : network) : Prop := exists h e, correct_entry client id i e /\ In e (log (nwState net h)).
Instance aiii : applied_implies_input_interface.
Proof using.
split.
exact applied_implies_input.
End AppliedImpliesInputProof.

Definition applied_implies_input_state_dec (net : network) : {applied_implies_input_state client id i net} + {~ applied_implies_input_state client id i net}.
unfold applied_implies_input_state.
destruct (aiis_host_dec net).
-
unfold aiis_host in *.
left.
repeat (break_exists; intuition).
eauto 10.
-
destruct (aiis_packet_dec net).
+
unfold aiis_packet in *.
left.
repeat (break_exists; intuition).
eauto 10.
+
unfold aiis_host, aiis_packet in *.
right.
intro.
repeat (break_exists; intuition); eauto 10.
