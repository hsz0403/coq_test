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

Lemma or_Comm: Commutativity L Gamma orp.
Proof.
constructor.
intros.
rewrite orp_comm.
Admitted.

Lemma prodp_comm {Comm: Commutativity L Gamma prodp}: forall x y, |-- prodp x y <--> prodp y x.
Proof.
intros.
Admitted.

Lemma left_unit {LU: LeftUnit L Gamma e prodp} : forall x, |-- prodp e x <--> x.
Proof.
intros.
apply solve_andp_intros.
+
apply left_unit1.
+
Admitted.

Lemma right_unit {RU: RightUnit L Gamma e prodp} : forall x, |-- prodp x e <--> x.
Proof.
intros.
apply solve_andp_intros.
+
apply right_unit1.
+
Admitted.

Lemma prodp_sump_distr_l {LDistr: LeftDistr L Gamma prodp sump}: forall x y z, |-- prodp x (sump y z) <--> sump (prodp x y) (prodp x z).
Proof.
intros.
apply solve_andp_intros.
+
apply left_distr1.
+
Admitted.

Lemma prodp_sump_distr_r {RDistr: RightDistr L Gamma prodp sump}: forall x y z, |-- prodp (sump y z) x <--> sump (prodp y x) (prodp z x).
Proof.
intros.
apply solve_andp_intros.
+
apply right_distr1.
+
Admitted.

Lemma Adjoint2RDistr: RightDistr L Gamma prodp orp.
Proof.
constructor; intros.
+
apply adjoint.
apply solve_orp_impp; apply adjoint.
-
apply orp_intros1.
-
apply orp_intros2.
+
apply solve_orp_impp.
-
apply prodp_mono1.
apply orp_intros1.
-
apply prodp_mono1.
Admitted.

Lemma Adjoint2LDistr {Comm: Commutativity L Gamma prodp}: LeftDistr L Gamma prodp orp.
Proof.
apply @RightDistr2LeftDistr; auto.
+
apply orp_Mono.
+
Admitted.

Lemma prodp_orp_distr_l: forall x y z: expr, |-- prodp (x || y) z <--> (prodp x z || prodp y z).
Proof.
intros.
Admitted.

Lemma prodp_orp_distr_r {Comm: Commutativity L Gamma prodp}: forall x y z: expr, |-- prodp x (y || z) <--> (prodp x y || prodp x z).
Proof.
intros.
Admitted.

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
Admitted.

Lemma funcp_andp_distr_r: forall x y z: expr, |-- funcp x (y && z) <--> (funcp x y && funcp x z).
Proof.
intros.
apply solve_andp_intros.
+
apply solve_impp_andp.
-
apply funcp_mono2.
apply andp_elim1.
-
apply funcp_mono2.
apply andp_elim2.
+
apply adjoint.
apply solve_impp_andp; apply adjoint.
-
apply andp_elim1.
-
Admitted.

Lemma falsep_prodp: forall x: expr, |-- prodp falsep x <--> falsep.
Proof.
intros.
apply solve_andp_intros.
+
apply adjoint.
apply falsep_elim.
+
Admitted.

Lemma prodp_falsep {Comm: Commutativity L Gamma prodp}: forall x: expr, |-- prodp x falsep <--> falsep.
Proof.
intros.
rewrite prodp_comm.
rewrite falsep_prodp.
Admitted.

Lemma prodp_iffp: forall x1 x2 y1 y2, |-- x1 <--> x2 -> |-- y1 <--> y2 -> |-- prodp x1 y1 <--> prodp x2 y2.
Proof.
intros.
apply solve_andp_intros.
+
apply prodp_mono.
-
eapply solve_andp_elim1; exact H.
-
eapply solve_andp_elim1; exact H0.
+
apply prodp_mono.
-
eapply solve_andp_elim2; exact H.
-
Admitted.

Lemma fold_left_iffp: forall x1 x2 xs1 xs2, (Forall2 (fun x1 x2 => |-- x1 <--> x2) xs1 xs2) -> |-- x1 <--> x2 -> |-- fold_left prodp xs1 x1 <--> fold_left prodp xs2 x2.
Proof.
intros.
apply solve_andp_intros.
+
apply fold_left_mono.
-
revert H; apply Forall2_impl.
intros.
eapply solve_andp_elim1; exact H.
-
eapply solve_andp_elim1; exact H0.
+
apply fold_left_mono.
-
apply Forall2_rev.
revert H; apply Forall2_impl.
intros.
eapply solve_andp_elim2; exact H.
-
Admitted.

Lemma fold_left_prodp_unfold {LU: LeftUnit L Gamma e prodp}: forall xs, |-- fold_left prodp xs e <--> match xs with | nil => e | x :: xs0 => fold_left prodp xs0 x end.
Proof.
intros.
destruct xs.
+
simpl.
apply provable_iffp_refl.
+
simpl.
apply fold_left_iffp.
-
induction xs.
*
constructor.
*
constructor; auto.
apply provable_iffp_refl.
-
Admitted.

Lemma fold_right_prodp_unfold {RU: RightUnit L Gamma e prodp}: forall xs, |-- fold_right prodp e xs <--> (fix f xs := match xs with | nil => e | x :: nil => x | x :: xs0 => prodp x (f xs0) end) xs.
Proof.
intros.
set (f := (fix f xs := match xs with | nil => e | x :: nil => x | x :: xs0 => prodp x (f xs0) end)).
destruct xs.
+
apply provable_iffp_refl.
+
simpl fold_right.
revert e0; induction xs; intros.
-
simpl.
rewrite right_unit.
apply provable_iffp_refl.
-
change (f (e0 :: a :: xs)) with (prodp e0 (f (a :: xs))).
apply prodp_iffp.
*
apply provable_iffp_refl.
*
Admitted.

Lemma prodp_assoc: forall x y z, |-- prodp x (prodp y z) <--> prodp (prodp x y) z.
Proof.
intros.
apply solve_andp_intros.
+
apply prodp_assoc1.
+
Admitted.

Lemma assoc_fold_left_fold_right_equiv: forall xs, |-- fold_left prodp xs e <--> fold_right prodp e xs.
Proof.
intros.
apply solve_andp_intros.
+
apply assoc_fold_left_fold_right.
+
Admitted.

Lemma assoc_prodp_fold_left_equiv: forall xs1 xs2, |-- prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e) <--> fold_left prodp (xs1 ++ xs2) e.
Proof.
intros.
apply solve_andp_intros.
+
apply assoc_prodp_fold_left.
+
Admitted.

Lemma orp_Mono: Monotonicity L Gamma orp.
Proof.
constructor; intros.
apply orp_proper_impp; auto.
