Set Implicit Arguments.
Require Import Notations.
Require Import Logic.
Require Import Datatypes.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Init.Wf.
Section Well_founded.
Variable A : Type.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Section FixPoint.
Variable P : A -> Type.
Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.
Variable EQ : forall a, P a -> P a -> Prop.
Variable Equiv: forall a: A, Equivalence (@EQ a).
Hypothesis F_ext : forall (x:A) (f g:forall y:A, R y x -> P y), (forall (y:A) (p:R y x), EQ (f y p) (g y p)) -> EQ (F f) (F g).
End FixPoint.
End Well_founded.

Lemma Fix_eq : forall x:A, EQ (Fix Rwf P F x) (F (fun (y:A) (p:R y x) => Fix Rwf P F y)).
Proof.
intro x; unfold Fix.
rewrite <- Fix_F_eq.
apply F_ext; intros.
Admitted.

Lemma Fix_F_inv : forall (x:A) (r s:Acc R x), EQ (Fix_F P F r) (Fix_F P F s).
Proof.
intro x; induction (Rwf x); intros.
rewrite <- (Fix_F_eq P F r); rewrite <- (Fix_F_eq P F s); intros.
apply F_ext; auto.
