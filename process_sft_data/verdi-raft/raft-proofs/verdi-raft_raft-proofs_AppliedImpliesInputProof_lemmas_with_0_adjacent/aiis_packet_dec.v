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

Definition aiis_packet_dec (net : network) : {aiis_packet net} + {~aiis_packet net}.
unfold aiis_packet.
apply exists_dec.
intros.
destruct (pBody x); try solve [right; intro; break_exists; intuition; discriminate].
simpl.
destruct (exists_dec _ _ correct_entry_dec l0); eauto.
right.
intro.
break_exists.
break_and.
find_inversion.
auto.
