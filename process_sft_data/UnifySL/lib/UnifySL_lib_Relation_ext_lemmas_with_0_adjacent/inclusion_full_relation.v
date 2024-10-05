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

Lemma inclusion_full_relation: forall {A} P, inclusion A P full_relation.
Proof.
intros.
hnf; intros.
hnf.
auto.
