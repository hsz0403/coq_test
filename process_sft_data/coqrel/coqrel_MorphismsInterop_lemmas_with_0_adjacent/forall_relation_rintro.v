Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import RelDefinitions.
Require Import RelOperators.
Require Import Relators.
Require Import Monotonicity.
Global Instance respectful_subrel A B: Monotonic (@respectful A B) (subrel --> subrel ++> subrel).
Proof.
firstorder.
Global Instance respectful_params: Params (@respectful) 4 := { }.
Hint Extern 0 (RIntro _ (respectful _ _) _ _) => eapply respectful_rintro : typeclass_instances.
Hint Extern 1 (RElim (respectful _ _) _ _ _ _) => eapply respectful_relim : typeclass_instances.
Global Instance forall_relation_subrel A P: Monotonic (@forall_relation A P) ((forallr -, subrel) ++> subrel).
Proof.
firstorder.
Global Instance forall_relation_params: Params (@forall_relation) 3 := { }.
Hint Extern 0 (RIntro _ (forall_relation _) _ _) => eapply forall_relation_rintro : typeclass_instances.
Hint Extern 1 (RElim (forall_relation _) _ _ _ _) => eapply forall_relation_relim : typeclass_instances.
Global Instance pointwise_relation_subrel A B: Monotonic (@pointwise_relation A B) (subrel ++> subrel).
Proof.
firstorder.
Global Instance pointwise_relation_params: Params (@pointwise_relation) 3 := { }.
Hint Extern 0 (RIntro _ (pointwise_relation _ _) _ _) => eapply pointwise_relation_rintro : typeclass_instances.
Hint Extern 1 (RElim (pointwise_relation _ _) _ _ _ _) => eapply pointwise_relation_relim : typeclass_instances.
Global Instance pointwise_relation_subrel_subrel A B: Related (pointwise_relation A (pointwise_relation B impl)) subrel subrel.
Proof.
firstorder.
Global Instance morphisms_proper_related {A} (R: relation A) (a: A): (normalization_done -> Proper R a) -> Monotonic a R | 10.
Proof.
firstorder.
Hint Immediate subrelation_subrel : typeclass_instances.
Ltac solve_morphisms_proper := match goal with | _ : normalization_done |- _ => fail 1 | H : apply_subrelation |- _ => clear H; red; rauto end.
Hint Extern 10 (Morphisms.Proper _ _) => solve_morphisms_proper : typeclass_instances.

Lemma forall_relation_rintro {A B} (R: forall a:A, relation (B a)) f g: RIntro (forall a, R a (f a) (g a)) (forall_relation R) f g.
Proof.
firstorder.
