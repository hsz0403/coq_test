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

Lemma GC_Ext_Classical_collapse_aux {sepcon_orp_AX: SepconOrAxiomatization L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} {ExtsGamma: ExtSeparationLogic L Gamma}: forall (x: expr), |-- x --> x * x.
Proof.
intros.
rewrite (sepcon_ext x) at 1.
assert (|-- TT --> x || ~~ x) by (apply solve_impp_elim_left, excluded_middle).
rewrite H; clear H.
rewrite sepcon_orp_distr_l.
apply solve_orp_impp; [apply provable_impp_refl |].
rewrite <- (andp_dup (x * ~~ x)).
rewrite sepcon_elim1 at 1.
rewrite sepcon_elim2 at 1.
AddSequentCalculus.
rewrite provable_derivable.
rewrite <- deduction_theorem.
apply deduction_falsep_elim.
apply deduction_modus_ponens with x.
+
apply deduction_andp_elim1 with (~~x).
solve_assum.
+
apply deduction_andp_elim2 with x.
solve_assum.
