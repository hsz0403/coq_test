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

Lemma hoare_while_partial_sound: forall b c B P, (forall s, s |= B <-> eval_bool s b) -> triple_partial_valid (P && B) c P -> triple_partial_valid P (Swhile b c) (P && ~~ B).
Proof.
intros.
unfold triple_partial_valid in *.
intros s ms ? ?.
apply access_Swhile in H2.
inversion H2; subst; clear H2; auto.
induction H3.
+
inversion H3.
-
subst.
auto.
-
subst.
eapply sat_mono; [eassumption |].
rewrite sat_andp.
split; auto.
unfold negp.
rewrite sat_impp; intros.
rewrite H in H6.
pose proof eval_bool_stable b _ _ H4.
simpl in H6, H7.
tauto.
+
assert (KRIPKE: s1 |= P0 && B) by (rewrite sat_andp; firstorder).
inversion H3.
-
subst.
apply lift_relation_forward in H4; subst.
auto.
-
subst.
eapply sat_mono in H6; [| eassumption].
inversion H4; subst.
specialize (H0 _ _ H6 H9).
destruct H5; subst; auto.
+
apply IHloop_access_fin; clear IHloop_access_fin H6.
assert (KRIPKE: s1 |= P0 && B) by (rewrite sat_andp; firstorder).
eapply sat_mono in H6; [| eassumption].
eapply sat_mono; [eassumption |].
exact (H0 _ _ H6 H4).
+
destruct H3.
subst; auto.
