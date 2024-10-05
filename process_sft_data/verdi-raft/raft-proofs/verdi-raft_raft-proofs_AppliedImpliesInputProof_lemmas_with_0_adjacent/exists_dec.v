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

Definition exists_dec : forall A (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) l, {exists x, P x /\ In x l} + {~ exists x, P x /\ In x l}.
intros.
destruct (find (fun e => if P_dec e then true else false) l) eqn:?.
-
find_apply_lem_hyp find_some.
intuition.
break_if; try discriminate.
eauto.
-
right.
intro.
break_exists.
intuition.
eapply find_none with (x := x) in Heqo; eauto.
break_if; congruence.
