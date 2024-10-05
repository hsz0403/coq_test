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

Lemma hoare_seq_partial_sound: forall c1 c2 P1 P2 P3, triple_partial_valid P1 c1 P2 -> triple_partial_valid P2 c2 P3 -> triple_partial_valid P1 (Ssequence c1 c2) P3.
Proof.
intros.
unfold triple_partial_valid in *.
intros s ms ? ?.
apply access_Ssequence in H2.
destruct H2 as [ms' [ms'' [? [? ?]]]].
specialize (H s ms' H1 H2).
destruct ms' as [| | s'].
+
inversion H.
+
inversion H3; subst ms''; clear H3.
inversion H4; auto.
+
inversion H3; subst.
-
apply lift_relation_forward in H4.
subst ms; auto.
-
eapply sat_mono in H; [| exact H6].
clear H2 H6 H3 s'; rename y into s'.
apply (H0 s' ms); auto.
inversion H4; auto.
