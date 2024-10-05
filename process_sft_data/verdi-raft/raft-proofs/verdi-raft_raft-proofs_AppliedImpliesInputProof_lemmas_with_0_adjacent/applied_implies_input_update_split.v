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

Lemma applied_implies_input_update_split : forall client id i net h d ps, applied_implies_input_state client id i (mkNetwork ps (update name_eq_dec (nwState net) h d)) -> exists e, correct_entry client id i e /\ (In e (log d) \/ (exists h, In e (log (nwState net h))) \/ (exists p es, In p ps /\ mEntries (pBody p) = Some es /\ In e es)).
Proof using.
unfold applied_implies_input_state.
intros.
break_exists_exists.
intuition.
break_exists.
simpl in *.
destruct (name_eq_dec h x0); rewrite_update; eauto.
