Require Export Lci.
Definition antisym (A : Set) (R : A -> A -> Prop) := forall x y : A, R x y -> R y x -> x = y :>A.
Definition pi1 : forall (A : Set) (P : A -> Prop), {x : A | P x} -> A.
Proof.
simple induction 1; auto.
Defined.
Definition inversible (S : Set) (Mult : S -> S -> S) (I x : S) := exists y : S, Mult x y = I /\ Mult y x = I.

Definition pi1 : forall (A : Set) (P : A -> Prop), {x : A | P x} -> A.
Proof.
simple induction 1; auto.
