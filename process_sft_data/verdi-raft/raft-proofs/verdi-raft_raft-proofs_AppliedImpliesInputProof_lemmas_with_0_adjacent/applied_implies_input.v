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

Lemma applied_implies_input : forall client id failed net tr e, @step_failure_star _ _ failure_params step_failure_init (failed, net) tr -> eClient e = client -> eId e = id -> applied_implies_input_state client id (eInput e) net -> in_input_trace client id (eInput e) tr.
Proof using.
intros.
pose proof @inverse_trace_relations_work _ _ step_failure (ITR client id (eInput e)) (failed, net) tr.
unfold step_failure_star in *.
simpl in *.
auto.
