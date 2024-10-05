Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.
Section soundness.
Existing Instance unit_kMD.
Context {P: ProgrammingLanguage} {MD: Model} {BSS: BigStepSemantics P model}.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {SM: Semantics L MD} {R: Relation model} {po_R: PreOrder Krelation} {kiSM: KripkeIntuitionisticSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM} {kminSM: KripkeMinimumSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM} {kpSM: KripkePropositionalSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}.
End soundness.

Lemma hoare_disjunction_total_sound: forall c P1 P2 Q1 Q2, triple_total_valid P1 c Q1 -> triple_total_valid P2 c Q2 -> triple_total_valid (P1 || P2) c (Q1 || Q2).
Proof.
intros.
unfold triple_total_valid in *.
intros.
specialize (H s_pre ms_post).
specialize (H0 s_pre ms_post).
rewrite sat_orp in H1.
destruct H1.
-
apply H in H1; auto.
destruct ms_post; auto.
rewrite sat_orp.
left.
assumption.
-
apply H0 in H1; auto.
destruct ms_post; auto.
rewrite sat_orp.
right.
assumption.
