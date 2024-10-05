Set Implicit Arguments.
Require Import Morphisms FinFun.
From Undecidability.HOU Require Import std.tactics.
Set Default Proof Using "Type".
Section ClosureRelations.
Variables (X: Type).
Implicit Types (R S: X -> X -> Prop) (x y z : X).
Notation "R <<= S" := (subrelation R S) (at level 70).
Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).
Definition functional R := forall x y z, R x y -> R x z -> y = z.
Inductive star R : X -> X -> Prop := | starRefl x : star R x x | starStep x x' y : R x x' -> star R x' y -> star R x y.
Inductive multiple R : X -> X -> Prop := | multipleSingle x y: R x y -> multiple R x y | multipleStep x x' y: R x x' -> multiple R x' y -> multiple R x y.
Inductive counted R : nat -> X -> X -> Prop := | countedRefl x: counted R 0 x x | countedStep x x' y n: R x x' -> counted R n x' y -> counted R (S n) x y.
Inductive sym R: X -> X -> Prop := | symId x y: R x y -> sym R x y | symInv x y: R y x -> sym R x y.
Hint Constructors star multiple counted : core.
Definition Normal R x := forall y, ~ R x y.
Definition evaluates R s t := star R s t /\ Normal R t.
Definition equiv R := star (sym R).
Fact Normal_star_stops R x: Normal R x -> forall y, star R x y -> x = y.
Proof.
destruct 2; firstorder.
Fact counted_trans R x y z m n: counted R m x y -> counted R n y z -> counted R (m + n) x z.
Proof.
induction 1; cbn; eauto.
Global Instance multiple_transitive R: Transitive (multiple R).
Proof.
intros ?; eapply multiple_trans.
Global Instance star_preorder R: PreOrder (star R).
Proof.
constructor; hnf; eauto using star_trans.
Global Instance star_exp R: R <<= star R.
Proof.
unfold subrelation; eauto.
Global Instance multiple_exp R: R <<= multiple R.
Proof.
unfold subrelation; eauto.
Fact counted_exp R: R === counted R 1.
Proof.
unfold subrelation; split; eauto.
intros x y H; inv H; inv H2; eauto.
Global Instance multiple_star R : multiple R <<= star R.
Proof.
induction 1; eauto.
Hint Resolve star_trans multiple_trans counted_trans star_exp multiple_exp counted_exp : core.
Global Instance star_mono R S : R <<= S -> star R <<= star S.
Proof.
intros H x y.
induction 1; eauto.
Global Instance multiple_mono R S : R <<= S -> multiple R <<= multiple S.
Proof.
intros H x y.
induction 1; eauto.
Global Instance eval_subrel R: (evaluates R) <<= (star R).
Proof.
intros x y [].
assumption.
Fact star_closure R S : PreOrder S -> R <<= S -> star R <<= S.
Proof.
intros H1 H2 x y.
induction 1 as [x|x x' y H4 _ IH].
-
reflexivity.
-
transitivity x'; auto.
Fact star_idem R : star (star R) === star R.
Proof.
split.
-
induction 1; eauto.
-
apply star_mono, star_exp.
Fact multiple_idem R : multiple (multiple R) === multiple R.
Proof.
split; eauto.
induction 1; eauto.
Fact multiple_fixpoint R : multiple (star R) === star R.
Proof.
split.
-
induction 1; eauto.
-
eauto.
Fact star_absorbtion R : star (multiple R) === star R.
Proof.
split.
-
induction 1; eauto.
apply multiple_destruct in H.
destruct H.
eauto.
-
eapply star_mono.
eauto.
Global Instance sym_Symmetric R: Symmetric (sym R).
Proof.
firstorder using sym_symmetric.
Global Instance equiv_star R: star R <<= equiv R.
Proof.
induction 1; unfold equiv in *; eauto using sym, star.
Global Instance equiv_rel R: R <<= equiv R.
Proof.
transitivity (star R); typeclasses eauto.
Global Instance equiv_equivalence R: Equivalence (equiv R).
Proof.
constructor; firstorder using refl_equiv, equiv_trans, equiv_symm.
Inductive starL R x: X -> Prop := | starReflL : starL R x x | starStepL y y': starL R x y -> R y y' -> starL R x y'.
Hint Constructors starL : core.
End ClosureRelations.
Hint Extern 4 => eapply subrel_unfold; [ typeclasses eauto |] : core.
Hint Constructors star multiple counted : core.
Hint Resolve star_trans multiple_trans counted_trans star_exp multiple_exp counted_exp equiv_join : core.

Fact Normal_star_stops R x: Normal R x -> forall y, star R x y -> x = y.
Proof.
Admitted.

Lemma star_trans R x y z : star R x y -> star R y z -> star R x z.
Proof.
Admitted.

Lemma multiple_trans R x y z : multiple R x y -> multiple R y z -> multiple R x z.
Proof.
Admitted.

Fact counted_trans R x y z m n: counted R m x y -> counted R n y z -> counted R (m + n) x z.
Proof.
Admitted.

Fact counted_exp R: R === counted R 1.
Proof.
unfold subrelation; split; eauto.
Admitted.

Lemma step_star_multiple R x y z: R x y -> star R y z -> multiple R x z.
Proof.
Admitted.

Lemma multiple_star_step R x y z : multiple R x y -> star R y z -> multiple R x z.
Proof.
intros [] % multiple_destruct ?.
eapply multiple_destruct.
Admitted.

Fact star_closure R S : PreOrder S -> R <<= S -> star R <<= S.
Proof.
intros H1 H2 x y.
induction 1 as [x|x x' y H4 _ IH].
-
reflexivity.
-
Admitted.

Fact star_idem R : star (star R) === star R.
Proof.
split.
-
induction 1; eauto.
-
Admitted.

Fact multiple_idem R : multiple (multiple R) === multiple R.
Proof.
split; eauto.
Admitted.

Fact multiple_fixpoint R : multiple (star R) === star R.
Proof.
split.
-
induction 1; eauto.
-
Admitted.

Fact star_absorbtion R : star (multiple R) === star R.
Proof.
split.
-
induction 1; eauto.
apply multiple_destruct in H.
destruct H.
eauto.
-
eapply star_mono.
Admitted.

Lemma sym_symmetric R x y: sym R x y -> sym R y x.
Proof.
Admitted.

Lemma refl_star R x y: x = y -> star R x y.
Proof.
Admitted.

Lemma refl_equiv R x: equiv R x x.
Proof.
Admitted.

Lemma equiv_trans R x y z: equiv R x y -> equiv R y z -> equiv R x z.
Proof.
Admitted.

Lemma equiv_symm R x y: equiv R x y -> equiv R y x.
Proof.
induction 1.
constructor; eauto.
eapply star_trans; eauto.
Admitted.

Lemma equiv_expand R x x' y y': star R x x' -> star R y y' -> equiv R x' y' -> equiv R x y.
Proof.
intros.
eapply equiv_trans.
eapply equiv_star, H.
eapply equiv_symm.
eapply equiv_trans.
eapply equiv_star, H0.
Admitted.

Lemma equiv_reduce R x x' y y' : star R x x' -> star R y y' -> equiv R x y -> equiv R x' y'.
Proof.
intros.
eapply equiv_trans.
eapply equiv_symm, equiv_star, H.
Admitted.

Lemma eq_equiv R (x y: X): x = y -> equiv R x y.
Proof.
Admitted.

Lemma equiv_join R x y z: star R x z -> star R y z -> equiv R x y.
Proof.
intros.
transitivity z.
rewrite H; reflexivity.
symmetry.
Admitted.

Lemma star_starL R x y : starL R x y <-> star R x y .
Proof.
split.
-
induction 1; auto.
induction IHstarL; eauto.
-
induction 1; eauto.
clear H0.
Admitted.

Lemma subrel_unfold R S (H: R <<= S) x y: R x y -> S x y.
Proof.
Admitted.

Lemma multiple_destruct R x y: multiple R x y <-> exists2 x', (R x x') & (star R x' y).
Proof.
split.
-
induction 1; eauto.
destruct IHmultiple; eexists; eauto.
-
intros [? H1 H2]; revert x H1; induction H2; eauto.
