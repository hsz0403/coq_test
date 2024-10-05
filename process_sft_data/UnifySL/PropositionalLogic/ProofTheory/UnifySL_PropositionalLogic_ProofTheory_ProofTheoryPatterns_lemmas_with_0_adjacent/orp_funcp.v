Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Section PatternInstances0.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma}.
End PatternInstances0.
Section DerivableRulesFromPatterns.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {prodp: expr -> expr -> expr}.
Section UnitTheorems.
Context {e: expr}.
End UnitTheorems.
Section DistrTheorems.
Context {sump: expr -> expr -> expr}.
End DistrTheorems.
Section AdjointTheorems.
Context {funcp: expr -> expr -> expr} {Adj: Adjointness L Gamma prodp funcp}.
End AdjointTheorems.
Section MonoTheorems.
Context {Mono: Monotonicity L Gamma prodp}.
Context {e: expr}.
End MonoTheorems.
Section AssocTheorems.
Context {e: expr} {Mono: Monotonicity L Gamma prodp} {Assoc: Associativity L Gamma prodp}.
Context {LU: LeftUnit L Gamma e prodp} {RU: RightUnit L Gamma e prodp}.
End AssocTheorems.
Section CommAssocTheorems.
Context {e: expr} {Mono: Monotonicity L Gamma prodp} {Comm: Commutativity L Gamma prodp} {Assoc: Associativity L Gamma prodp}.
End CommAssocTheorems.
End DerivableRulesFromPatterns.
Section ProofTheoryPatterns.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma}.
End ProofTheoryPatterns.
Section PatternInstances.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma}.
End PatternInstances.
Section DerivableRules.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma}.
Definition multi_and (xs: list expr): expr := fold_left andp xs truep.
End DerivableRules.

Lemma orp_funcp {Comm: Commutativity L Gamma prodp}: forall x y z: expr, |-- funcp (x || y) z <--> (funcp x z && funcp y z).
Proof.
pose proof Adjoint2Mono as Mono.
intros.
apply solve_andp_intros.
+
apply solve_impp_andp.
-
apply funcp_mono.
*
apply orp_intros1.
*
apply provable_impp_refl.
-
apply funcp_mono.
*
apply orp_intros2.
*
apply provable_impp_refl.
+
apply adjoint.
rewrite prodp_orp_distr_r.
apply solve_orp_impp; apply adjoint.
-
apply andp_elim1.
-
apply andp_elim2.
