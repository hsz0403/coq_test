Require Export Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Coq.Setoids.Setoid.
Definition full_relation {A} : relation A := fun _ _ => True.
Instance same_relation_Equivalence {A}: Equivalence (same_relation A).
Proof.
split.
+
apply same_relation_Reflexive.
+
apply same_relation_Symmetric.
+
apply same_relation_Transitive.
Instance inclusion_proper {A}: Proper (same_relation A ==> same_relation A ==> iff) (inclusion A).
Proof.
intros.
do 2 (hnf; intros ?F ?G ?H).
unfold inclusion.
rewrite same_relation_spec in H, H0.
split; intros HH x y; specialize (HH x y).
+
rewrite (H x y), (H0 x y) in HH.
auto.
+
rewrite (H x y), (H0 x y).
auto.
Inductive compond_relation {A: Type} (R1 R2: relation A) : relation A := | compond_intro: forall x y z, R1 x y -> R2 y z -> compond_relation R1 R2 x z.
Instance compond_relation_proper {A: Type}: Proper (same_relation A ==> same_relation A ==> same_relation A) compond_relation.
Proof.
do 2 (hnf; intros).
destruct H, H0.
split; apply compond_relation_inclusion; auto.
Defined.
Instance relation_conjunction_proper {A: Type}: Proper (same_relation A ==> same_relation A ==> same_relation A) relation_conjunction.
Proof.
do 2 (hnf; intros).
destruct H, H0.
split; apply relation_conjunction_inclusion; auto.
Defined.
Definition respectful_relation {A B} (f: A -> B) (R: relation B): relation A := fun x y => R (f x) (f y).
Definition fst_relation {A B}: relation A -> relation (A * B) := respectful_relation (@fst A B).
Definition snd_relation {A B}: relation B -> relation (A * B) := respectful_relation (@snd A B).
Instance respectful_relation_proper {A B} (f: A -> B): Proper (same_relation _ ==> same_relation _) (respectful_relation f).
Proof.
hnf; intros.
rewrite @same_relation_spec in H |- *.
intros b1 b2.
unfold respectful_relation.
apply H.
Defined.
Definition partial_functional {A: Type} (R: relation A): Prop := forall m n n', R m n -> R m n' -> n = n'.
Class PartialFunctional {A: Type} (R: relation A): Prop := partial_functionality: forall m n n', R m n -> R m n' -> n = n'.
Definition functional {A: Type} (R: relation A): Prop := forall m, exists n, forall n', R m n' <-> n' = n.
Class Functional {A: Type} (R: relation A): Prop := functionality: forall m, exists n, forall n', R m n' <-> n' = n.
Definition serial {A: Type} (R: relation A): Prop := forall m, exists n, R m n.
Class Serial {A: Type} (R: relation A): Prop := seriality: forall m, exists n, R m n.
Instance Functional_PartialFunctional {A: Type} {R: relation A} {_: Functional R}: PartialFunctional R.
Proof.
intros; hnf; intros.
destruct (functionality m) as [n0 ?].
rewrite H2 in H0, H1.
congruence.
Instance Functional_Serial {A: Type} {R: relation A} {_: Functional R}: Serial R.
Proof.
intros; hnf; intros.
destruct (functionality m) as [n ?].
exists n.
rewrite H0.
auto.
Class Inclusion {A: Type} (R1 R2: relation A) : Prop := including: forall a b, R1 a b -> R2 a b.

Lemma same_relation_spec: forall {A} a1 a2, same_relation A a1 a2 <-> pointwise_relation A (pointwise_relation A iff) a1 a2.
Proof.
intros.
unfold same_relation, inclusion, pointwise_relation.
Admitted.

Lemma same_relation_Reflexive {A}: Reflexive (same_relation A).
Proof.
hnf; intros.
rewrite same_relation_spec.
unfold pointwise_relation.
Admitted.

Lemma same_relation_Symmetric {A}: Symmetric (same_relation A).
Proof.
hnf; intros.
rewrite same_relation_spec in *.
unfold pointwise_relation in *.
Admitted.

Lemma same_relation_Transitive {A}: Transitive (same_relation A).
Proof.
hnf; intros.
rewrite same_relation_spec in H, H0 |- *.
unfold pointwise_relation in *.
intros.
rewrite H, H0.
Admitted.

Instance same_relation_Equivalence {A}: Equivalence (same_relation A).
Proof.
split.
+
apply same_relation_Reflexive.
+
apply same_relation_Symmetric.
+
Admitted.

Instance inclusion_proper {A}: Proper (same_relation A ==> same_relation A ==> iff) (inclusion A).
Proof.
intros.
do 2 (hnf; intros ?F ?G ?H).
unfold inclusion.
rewrite same_relation_spec in H, H0.
split; intros HH x y; specialize (HH x y).
+
rewrite (H x y), (H0 x y) in HH.
auto.
+
rewrite (H x y), (H0 x y).
Admitted.

Lemma app_same_relation: forall {A: Type} (R1 R2: relation A) (a1 a2: A), same_relation A R1 R2 -> (R1 a1 a2 <-> R2 a1 a2).
Proof.
intros.
rewrite same_relation_spec in H.
specialize (H a1 a2).
Admitted.

Lemma compond_relation_spec: forall {A} (R1 R2: relation A) x z, compond_relation R1 R2 x z -> exists y, R1 x y /\ R2 y z.
Proof.
intros.
inversion H; subst.
Admitted.

Lemma compond_relation_inclusion: forall {A} (R1 R2 R3 R4: relation A), inclusion _ R1 R2 -> inclusion _ R3 R4 -> inclusion _ (compond_relation R1 R3) (compond_relation R2 R4).
Proof.
intros.
hnf; intros.
inversion H1; subst.
Admitted.

Instance compond_relation_proper {A: Type}: Proper (same_relation A ==> same_relation A ==> same_relation A) compond_relation.
Proof.
do 2 (hnf; intros).
destruct H, H0.
Admitted.

Lemma compond_assoc: forall {A: Type} (R1 R2 R3: relation A), same_relation _ (compond_relation (compond_relation R1 R2) R3) (compond_relation R1 (compond_relation R2 R3)).
Proof.
intros.
Admitted.

Lemma compond_eq_right: forall {A: Type} (R: relation A), same_relation _(compond_relation R eq) R.
Proof.
intros.
split; hnf; intros.
+
inversion H; subst.
auto.
+
Admitted.

Lemma compond_eq_left: forall {A: Type} (R: relation A), same_relation _(compond_relation eq R) R.
Proof.
intros.
split; hnf; intros.
+
inversion H; subst.
auto.
+
Admitted.

Lemma relation_conjunction_inclusion: forall {A} (R1 R2 R3 R4: relation A), inclusion _ R1 R2 -> inclusion _ R3 R4 -> inclusion _ (relation_conjunction R1 R3) (relation_conjunction R2 R4).
Proof.
intros.
hnf; intros.
inversion H1; subst.
Admitted.

Instance relation_conjunction_proper {A: Type}: Proper (same_relation A ==> same_relation A ==> same_relation A) relation_conjunction.
Proof.
do 2 (hnf; intros).
destruct H, H0.
Admitted.

Lemma relation_conjunction_iff: forall {A} (R R': relation A) x y, relation_conjunction R R' x y <-> R x y /\ R' x y.
Proof.
intros.
Admitted.

Lemma relation_disjunction_iff: forall {A} (R R': relation A) x y, relation_disjunction R R' x y <-> R x y \/ R' x y.
Proof.
intros.
Admitted.

Lemma relation_disjunction_inclusion_left: forall {A} (R R': relation A), inclusion _ R (relation_disjunction R R').
Proof.
intros.
intros ? ? ?.
rewrite relation_disjunction_iff.
Admitted.

Lemma relation_disjunction_inclusion_right: forall {A} (R R': relation A), inclusion _ R' (relation_disjunction R R').
Proof.
intros.
intros ? ? ?.
rewrite relation_disjunction_iff.
Admitted.

Instance respectful_relation_proper {A B} (f: A -> B): Proper (same_relation _ ==> same_relation _) (respectful_relation f).
Proof.
hnf; intros.
rewrite @same_relation_spec in H |- *.
intros b1 b2.
unfold respectful_relation.
Admitted.

Lemma function_Functional {A: Type} {f: A -> A}: Functional (fun a => eq (f a)).
Proof.
hnf; intros.
exists (f m); intros.
Admitted.

Lemma SerialPartialFunctional_Functional {A: Type} {R: relation A}: Serial R -> PartialFunctional R -> Functional R.
Proof.
intros; hnf; intros.
destruct (seriality m) as [n ?].
exists n; intros.
split; intros.
+
eapply partial_functionality; eauto.
+
Admitted.

Instance Functional_PartialFunctional {A: Type} {R: relation A} {_: Functional R}: PartialFunctional R.
Proof.
intros; hnf; intros.
destruct (functionality m) as [n0 ?].
rewrite H2 in H0, H1.
Admitted.

Instance Functional_Serial {A: Type} {R: relation A} {_: Functional R}: Serial R.
Proof.
intros; hnf; intros.
destruct (functionality m) as [n ?].
exists n.
rewrite H0.
Admitted.

Lemma respectful_compond_relation: forall {A B} (f: A -> B) R1 R2, inclusion _ (compond_relation (respectful_relation f R1) (respectful_relation f R2)) (respectful_relation f (compond_relation R1 R2)).
Proof.
intros.
intros a1 a2 ?.
inversion H; subst.
apply compond_intro with (f y); auto.
