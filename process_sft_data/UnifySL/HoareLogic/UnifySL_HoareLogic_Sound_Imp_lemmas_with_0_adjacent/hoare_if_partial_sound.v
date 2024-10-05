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
Section partial_soundness.
Existing Instance unit_kMD.
Import Partial.
Context {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {MD: Model} {R: Relation model} {po_R: PreOrder Krelation} {BSS: BigStepSemantics P model} {iBSS: ImpBigStepSemantics P model BSS}.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {kminSM: KripkeMinimumSemantics L MD tt SM} {kpSM: KripkePropositionalSemantics L MD tt SM}.
End partial_soundness.
Section total_soundness.
Existing Instance unit_kMD.
Import Total.
Context {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {MD: Model} {R: Relation model} {po_R: PreOrder Krelation} {BSS: BigStepSemantics P model} {iBSS: ImpBigStepSemantics P model BSS}.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {kminSM: KripkeMinimumSemantics L MD tt SM} {kpSM: KripkePropositionalSemantics L MD tt SM}.
End total_soundness.

Lemma hoare_if_partial_sound: forall b c1 c2 B P1 P2, (forall s, s |= B <-> eval_bool s b) -> triple_partial_valid (P1 && B) c1 P2 -> triple_partial_valid (P1 && ~~ B) c2 P2 -> triple_partial_valid P1 (Sifthenelse b c1 c2) P2.
Proof.
intros.
unfold triple_partial_valid in *.
intros s ms ? ?.
apply access_Sifthenelse in H3.
destruct H3 as [[? [s' [? ?]]] | [? [s' [? ?]]]].
+
assert (KRIPKE: s |= P1 && B) by (rewrite sat_andp; firstorder).
inversion H4; subst.
-
apply lift_relation_forward in H5; subst; auto.
-
eapply sat_mono in H6; [| eassumption].
inversion H5; subst.
apply (H0 y); auto.
+
assert (KRIPKE: s |= P1 && ~~ B).
{
rewrite sat_andp; split; auto.
unfold negp; rewrite sat_impp.
intros.
rewrite H in H7.
pose proof eval_bool_stable b _ _ H6.
simpl in H7, H8.
rewrite <- H8 in H7; exfalso; auto.
}
inversion H4; subst.
-
apply lift_relation_forward in H5; subst; auto.
-
eapply sat_mono in H6; [| eassumption].
inversion H5; subst.
apply (H1 y); auto.
