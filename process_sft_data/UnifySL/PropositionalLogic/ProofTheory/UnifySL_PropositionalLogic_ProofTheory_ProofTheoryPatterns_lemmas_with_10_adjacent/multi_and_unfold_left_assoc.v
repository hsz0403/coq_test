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

Lemma andp_Mono: Monotonicity L Gamma andp.
Proof.
eapply @Adjoint2Mono.
+
auto.
+
apply impp_andp_Adjoint.
+
Admitted.

Lemma andp_LU: LeftUnit L Gamma TT andp.
Proof.
intros.
apply Build_LeftUnit'.
intros.
Admitted.

Lemma andp_RU: RightUnit L Gamma TT andp.
Proof.
intros.
apply Build_RightUnit'.
intros.
Admitted.

Lemma andp_Assoc: Associativity L Gamma andp.
Proof.
intros.
apply Build_Associativity'.
intros.
Admitted.

Lemma falsep_andp: forall x: expr, |-- FF && x <--> FF.
Proof.
intros.
Admitted.

Lemma andp_falsep: forall x: expr, |-- x && FF <--> FF.
Proof.
intros.
Admitted.

Lemma andp_orp_distr_l: forall x y z: expr, |-- (x || y) && z <--> (x && z) || (y && z).
Proof.
intros.
Admitted.

Lemma andp_orp_distr_r: forall x y z: expr, |-- x && (y || z) <--> (x && y) || (x && z).
Proof.
intros.
Admitted.

Lemma multi_and_spec: forall (xs: list expr), |-- multi_and xs <--> fold_right andp TT xs.
Proof.
intros.
unfold multi_and.
pose proof @assoc_fold_left_fold_right_equiv _ _ _ _ _ _ andp TT andp_Mono andp_Assoc andp_LU andp_RU.
Admitted.

Lemma multi_and_unfold_right_assoc: forall (xs: list expr), |-- multi_and xs <--> (fix f xs := match xs with | nil => TT | x :: nil => x | x :: xs0 => x && (f xs0) end) xs.
Proof.
intros.
rewrite multi_and_spec.
pose proof @fold_right_prodp_unfold _ _ _ _ _ _ andp andp_Mono TT andp_RU.
Admitted.

Lemma multi_and_multi_imp: forall (xs: list expr) (y: expr), |-- (multi_and xs --> y) <--> (multi_imp xs y).
Proof.
intros.
unfold multi_imp.
rewrite multi_and_spec.
induction xs as [| x xs].
+
simpl.
apply truep_impp.
+
simpl.
rewrite <- impp_curry_uncurry.
apply impp_proper_iffp; [apply provable_iffp_refl |].
Admitted.

Lemma multi_and_unfold_left_assoc: forall (xs: list expr), |-- multi_and xs <--> match xs with | nil => TT | x :: xs0 => (fix f xs x := match xs with | nil => x | x0 :: xs0 => f xs0 (x && x0) end) xs0 x end.
Proof.
intros.
pose proof @fold_left_prodp_unfold _ _ _ _ _ _ andp andp_Mono TT andp_LU.
apply H.
