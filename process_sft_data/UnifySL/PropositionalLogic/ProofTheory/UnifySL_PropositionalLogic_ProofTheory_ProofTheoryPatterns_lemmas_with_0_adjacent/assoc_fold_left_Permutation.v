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

Lemma assoc_fold_left_Permutation: forall x ys1 ys2, Permutation ys1 ys2 -> |-- fold_left prodp ys1 x <--> fold_left prodp ys2 x.
Proof.
intros.
pose proof @proper_permutation_fold_left _ _ _ _ prodp.
assert (forall x y, |-- x <--> y -> forall z1 z2, z1 = z2 -> |-- prodp x z1 <--> prodp y z2) by (intros; subst; apply prodp_iffp; [auto | apply provable_iffp_refl]).
specialize (H0 H1); clear H1.
assert (forall x1 x2 y z, |-- x1 <--> x2 -> |-- prodp (prodp x1 y) z <--> prodp (prodp x2 z) y).
{
intros.
rewrite <- !prodp_assoc.
apply prodp_iffp; [auto | apply prodp_comm].
}
specialize (H0 H1); clear H1.
apply H0; auto.
apply provable_iffp_refl.
