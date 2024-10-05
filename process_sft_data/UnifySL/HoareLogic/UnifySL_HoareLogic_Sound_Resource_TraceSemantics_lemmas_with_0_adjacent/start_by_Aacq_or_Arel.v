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

Lemma start_by_Aacq_or_Arel {Ac: Action} {Res: Resource} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res}: forall r tr, start_by_Aacq r tr -> start_by_Arel r tr -> False.
Proof.
intros.
induction tr.
+
inversion H0.
+
destruct (classic (is_resource_action r a)) as [[? | ?] | ?]; subst.
-
inversion H0; subst; solve_resource_action.
-
inversion H; subst; solve_resource_action.
-
inversion H; subst; solve_resource_action.
inversion H0; subst; solve_resource_action.
auto.
