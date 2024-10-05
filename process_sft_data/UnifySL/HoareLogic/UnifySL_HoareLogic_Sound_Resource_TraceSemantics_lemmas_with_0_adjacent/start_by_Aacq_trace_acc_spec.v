Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.TraceSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.
Require Import Logic.HoareLogic.GuardedHoareTriple_TraceSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.
Section soundness.
Existing Instance unit_kMD.
Context {P: ProgrammingLanguage} {MD: Model} {J: Join model} {SA: SeparationAlgebra model} {R: Relation model} {po_R: PreOrder Krelation} {DCSA: DownwardsClosedSeparationAlgebra model} {UCSA: UpwardsClosedSeparationAlgebra model} {Res: Resource} {Ac: Action} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res} {TS: TraceSemantics P (resources * model) Ac} {AIr: ActionInterpret_resource model Ac Res ac_sem} {SAAIr: @SAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (fun a => ~ is_resources_action a)} {KAIr: @KActionInterpret_resource (resources * model) Ac ac_sem (RelProd (discPred_R resource) R)}.
Instance KSAAIr: @KSAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R) (fun a => ~ is_resources_action a) := ordered_and_frame_AIr _ _ _.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsepconSM: FlatSemantics.SepconSemantics L MD tt SM}.
Class LegalInvariants (Inv: resource * (model -> Prop) -> Prop): Prop := { at_most_one_invariant: forall r I1 I2, Inv (r, I1) -> Inv (r, I2) -> I1 = I2; invariant_mono: forall r I, Inv (r, I) -> forall s1 s2, I s1 -> s1 <= s2 -> I s2; invariant_precise: forall r I, Inv (r, I) -> forall s, (exists s', (fun s' => exists f, I f /\ join s' f s) s') -> (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s') }.
End soundness.

Lemma start_by_Aacq_trace_acc_spec {state: Type} {Ac: Action} {Res: Resource} {J: Join state} {state_R: Relation state} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res} {ac_sem: ActionInterpret (resources * state) Ac} {AIr: ActionInterpret_resource state Ac Res ac_sem}: forall (Inv: resource * (state -> Prop) -> Prop) (tr: trace) A1 A2 s1 s2, (forall r, start_by_Aacq r tr) -> @trace_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) tr (A1, s1) (Terminating (A2, s2)) -> A1 = A2.
Proof.
intros.
assert (join A2 (fun r => start_by_Arel r tr) A1).
2: {
extensionality r; apply prop_ext.
specialize (H r); specialize (H1 r).
pose proof start_by_Aacq_or_Arel r tr.
destruct H1; tauto.
}
assert (forall r, start_by_Aacq r tr \/ start_by_Arel r tr).
{
intros r.
specialize (H r).
auto.
}
clear H.
revert s1 A1 H0; induction tr; intros.
+
inversion H0; subst; clear H0.
clear - nAcr.
intros r.
pose proof start_by_Aacq_or_Arel r nil.
pose proof start_by_Aacq_nil r.
split; tauto.
+
inversion H0; subst; clear H0.
destruct s' as [A1' s1'].
specialize (fun HH => IHtr HH s1' A1' H6); clear H6.
simpl in H3.
assert (HH: forall r : resource, start_by_Aacq r tr \/ start_by_Arel r tr).
{
clear - nAcr H1.
intros r; specialize (H1 r).
destruct (classic (is_resource_action r a)) as [[? | ?] | ?]; subst; destruct H1 as [HH | HH]; inversion HH; auto.
}
specialize (IHtr HH); clear HH.
intros r; specialize (IHtr r); specialize (H1 r).
destruct (classic (is_resources_action a)) as [[?r [? | ?]] | ?]; subst.
-
inversion H3; subst; clear H3; solve_resource_action.
clear I f H7 H8 H9.
specialize (H6 r).
pose proof start_by_Aacq_or_Arel r (Aacquire_res r0 :: tr).
pose proof start_by_Aacq_or_Arel r tr.
destruct H1 as [H1 | H1]; inversion H1; subst; solve_resource_action; destruct IHtr, H6; split; try tauto.
-
inversion H3; subst; clear H3; solve_resource_action.
clear I H7 H8.
specialize (H6 r).
pose proof start_by_Aacq_or_Arel r (Arelease_res r0 :: tr).
pose proof start_by_Aacq_or_Arel r tr.
destruct H1 as [H1 | H1]; inversion H1; subst; solve_resource_action; destruct IHtr, H6; split; try tauto.
-
rewrite <- thread_local_state_enable_non_resource_action in H3 by auto.
apply state_enable_non_resource_action1 in H3; auto.
subst A1.
assert (~ is_resource_action r a) by (intro HH; apply H; exists r; auto).
pose proof start_by_Aacq_or_Arel r (a :: tr).
pose proof start_by_Aacq_or_Arel r tr.
destruct H1 as [H1 | H1]; inversion H1; subst; solve_resource_action; destruct IHtr; split; try tauto.
