Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Section DerivedRules.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {sepconAX: SepconAxiomatization L Gamma}.
Context {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma}.
End DerivedRules.

Lemma provable_sepcon_andp_left: forall (x y z: expr), |-- (x && y) * z --> (x * z) && (y * z).
Proof.
intros.
apply solve_impp_andp.
+
apply sepcon_mono.
-
apply andp_elim1.
-
apply provable_impp_refl.
+
apply sepcon_mono.
-
apply andp_elim2.
-
apply provable_impp_refl.
