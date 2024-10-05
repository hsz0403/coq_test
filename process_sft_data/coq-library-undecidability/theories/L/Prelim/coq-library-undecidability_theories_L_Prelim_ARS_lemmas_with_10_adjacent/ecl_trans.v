Require Export Undecidability.Shared.Libs.PSL.Base Lia.
Module ARSNotations.
Notation "p '<=1' q" := (forall x, p x -> q x) (at level 70).
Notation "p '=1' q" := (forall x, p x <-> q x) (at level 70).
Notation "R '<=2' S" := (forall x y, R x y -> S x y) (at level 70).
Notation "R '=2' S" := (forall x y, R x y <-> S x y) (at level 70).
End ARSNotations.
Import ARSNotations.
Definition rcomp X Y Z (R : X -> Y -> Prop) (S : Y -> Z -> Prop) : X -> Z -> Prop := fun x z => exists y, R x y /\ S y z.
Require Import Arith.
Definition pow X R n : X -> X -> Prop := it (rcomp R) n eq.
Definition functional {X Y} (R: X -> Y -> Prop) := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.
Definition terminal {X Y} (R: X -> Y -> Prop) x:= forall y, ~ R x y.
Section FixX.
Variable X : Type.
Implicit Types R S : X -> X -> Prop.
Implicit Types x y z : X.
Definition reflexive R := forall x, R x x.
Definition symmetric R := forall x y, R x y -> R y x.
Definition transitive R := forall x y z, R x y -> R y z -> R x z.
Inductive star R : X -> X -> Prop := | starR x : star R x x | starC x y z : R x y -> star R y z -> star R x z.
Definition evaluates R x y := star R x y /\ terminal R y.
Instance star_PO R: PreOrder (star R).
Proof.
constructor;repeat intro;try eapply star_trans; now eauto using star.
Inductive ecl R : X -> X -> Prop := | eclR x : ecl R x x | eclC x y z : R x y -> ecl R y z -> ecl R x z | eclS x y z : R y x -> ecl R y z -> ecl R x z.
Definition joinable R x y := exists z, R x z /\ R y z.
Definition diamond R := forall x y z, R x y -> R x z -> joinable R y z.
Definition confluent R := diamond (star R).
Definition semi_confluent R := forall x y z, R x y -> star R x z -> joinable (star R) y z.
Definition church_rosser R := ecl R <=2 joinable (star R).
Goal forall R, diamond R -> semi_confluent R.
Proof.
intros R A x y z B C.
revert x C y B.
refine (star_simpl_ind _ _).
-
intros y C.
exists y.
eauto using star.
-
intros x x' C D IH y E.
destruct (A _ _ _ C E) as [v [F G]].
destruct (IH _ F) as [u [H I]].
assert (J:= starC G H).
exists u.
eauto using star.
Definition uniform_confluent (R : X -> X -> Prop ) := forall s t1 t2, R s t1 -> R s t2 -> t1 = t2 \/ exists u, R t1 u /\ R t2 u.
Definition classical R x := terminal R x \/ exists y, R x y.
Inductive SN R : X -> Prop := | SNC x : (forall y, R x y -> SN R y) -> SN R x.
Fact SN_unfold R x : SN R x <-> forall y, R x y -> SN R y.
Proof.
split.
-
destruct 1 as [x H].
exact H.
-
intros H.
constructor.
exact H.
End FixX.
Existing Instance star_PO.
Inductive redWithMaxSize {X} (size:X -> nat) (step : X -> X -> Prop): nat -> X -> X -> Prop:= redWithMaxSizeR m s: m = size s -> redWithMaxSize size step m s s | redWithMaxSizeC s s' t m m': step s s' -> redWithMaxSize size step m' s' t -> m = max (size s) m' -> redWithMaxSize size step m s t.
Instance ecl_Equivalence {X} (R:X->X->Prop) : Equivalence (ecl R).
Proof.
split.
-
constructor.
-
apply ecl_sym.
-
apply ecl_trans.
Instance star_ecl_subrel {X} (R:X->X->Prop) : subrelation (star R) (ecl R).
Proof.
intro.
eapply star_ecl.
Instance pow_ecl_subrel {X} (R:X->X->Prop) n : subrelation (pow R n) (ecl R).
Proof.
intros ? ? H%pow_star.
now rewrite H.
Definition computesRel {X Y} (f : X -> option Y) (R:X -> Y -> Prop) := forall x, match f x with Some y => R x y | None => terminal R x end.
Definition evaluatesIn (X : Type) (R : X -> X -> Prop) n (x y : X) := pow R n x y /\ terminal R y.

Lemma star_simpl_ind R (p : X -> Prop) y : p y -> (forall x x', R x x' -> star R x' y -> p x' -> p x) -> forall x, star R x y -> p x.
Proof.
intros A B.
Admitted.

Lemma star_trans R: transitive (star R).
Proof.
Admitted.

Lemma R_star R: R <=2 star R.
Proof.
Admitted.

Instance star_PO R: PreOrder (star R).
Proof.
Admitted.

Lemma star_pow R x y : star R x y <-> exists n, pow R n x y.
Proof.
split; intros A.
-
induction A as [|x x' y B _ [n IH]].
+
exists 0.
reflexivity.
+
exists (S n), x'.
auto.
-
destruct A as [n A].
revert x A.
induction n; intros x A.
+
destruct A.
constructor.
+
destruct A as [x' [A B]].
Admitted.

Lemma pow_star R x y n: pow R n x y -> star R x y.
Proof.
intros A.
erewrite star_pow.
Admitted.

Lemma ecl_sym R : symmetric (ecl R).
Proof.
Admitted.

Lemma star_ecl R : star R <=2 ecl R.
Proof.
Admitted.

Goal forall R, diamond R -> semi_confluent R.
Proof.
intros R A x y z B C.
revert x C y B.
refine (star_simpl_ind _ _).
-
intros y C.
exists y.
eauto using star.
-
intros x x' C D IH y E.
destruct (A _ _ _ C E) as [v [F G]].
destruct (IH _ F) as [u [H I]].
assert (J:= starC G H).
exists u.
Admitted.

Lemma diamond_to_semi_confluent R : diamond R -> semi_confluent R.
Proof.
intros A x y z B C.
revert y B.
induction C as [|x x' z D _ IH]; intros y B.
-
exists y.
eauto using star.
-
destruct (A _ _ _ B D) as [v [E F]].
destruct (IH _ F) as [u [G H]].
exists u.
Admitted.

Lemma semi_confluent_confluent R : semi_confluent R <-> confluent R.
Proof.
split; intros A x y z B C.
-
revert y B.
induction C as [|x x' z D _ IH]; intros y B.
+
exists y.
eauto using star.
+
destruct (A _ _ _ D B) as [v [E F]].
destruct (IH _ E) as [u [G H]].
exists u.
eauto using (@star_trans R).
-
Admitted.

Lemma diamond_to_confluent R : diamond R -> confluent R.
Proof.
intros A.
Admitted.

Lemma confluent_CR R : church_rosser R <-> confluent R.
Proof.
split; intros A.
-
intros x y z B C.
apply A.
eauto using (@ecl_trans R), star_ecl, (@ecl_sym R).
-
intros x y B.
apply semi_confluent_confluent in A.
induction B as [x|x x' y C B IH|x x' y C B IH].
+
exists x.
eauto using star.
+
destruct IH as [z [D E]].
exists z.
eauto using star.
+
destruct IH as [u [D E]].
destruct (A _ _ _ C D) as [z [F G]].
exists z.
Admitted.

Lemma functional_uc R : functional R -> uniform_confluent R.
Proof.
intros F ? ? ? H1 H2.
left.
eapply F.
Admitted.

Lemma pow_add R n m (s t : X) : pow R (n + m) s t <-> rcomp (pow R n) (pow R m) s t.
Proof.
revert m s t; induction n; intros m s t.
-
simpl.
split; intros.
econstructor.
split.
unfold pow.
simpl.
reflexivity.
eassumption.
destruct H as [u [H1 H2]].
unfold pow in H1.
simpl in *.
subst s.
eassumption.
-
simpl in *; split; intros.
+
destruct H as [u [H1 H2]].
change (it (rcomp R) (n + m) eq) with (pow R (n+m)) in H2.
rewrite IHn in H2.
destruct H2 as [u' [A B]].
unfold pow in A.
econstructor.
split.
econstructor.
repeat split; repeat eassumption.
eassumption.
+
destruct H as [u [H1 H2]].
destruct H1 as [u' [A B]].
econstructor.
split.
eassumption.
change (it (rcomp R) (n + m) eq) with (pow R (n + m)).
rewrite IHn.
econstructor.
Admitted.

Lemma rcomp_eq (R S R' S' : X -> X -> Prop) (s t : X) : (R =2 R') -> (S =2 S') -> (rcomp R S s t <-> rcomp R' S' s t).
Proof.
intros A B.
Admitted.

Lemma ecl_trans R : transitive (ecl R).
Proof.
induction 1; eauto using ecl.
