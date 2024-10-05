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

Lemma handleInputs_aais : forall client id h inp i net os d' ms e o, ~ applied_implies_input_state client id i net -> handleInput h inp (nwState net h) = (os, d', ms) -> correct_entry client id i e -> In e (log d') -> in_input_trace client id i [(h, inl inp); o].
Proof using.
intros.
destruct inp; simpl in *.
-
find_erewrite_lem handleTimeout_log.
exfalso.
eauto using aiis_intro_state.
-
destruct (log d') using (handleClientRequest_log_ind ltac:(eauto)).
+
exfalso.
eauto using aiis_intro_state.
+
simpl in *.
break_or_hyp.
*
subst.
unfold in_input_trace.
unfold correct_entry in *.
break_and.
subst.
simpl.
eauto.
*
exfalso.
eauto using aiis_intro_state.
