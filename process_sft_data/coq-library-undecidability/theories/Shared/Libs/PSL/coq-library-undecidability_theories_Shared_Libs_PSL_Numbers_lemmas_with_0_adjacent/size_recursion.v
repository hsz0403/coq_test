From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import EqDec.
Instance nat_le_dec (x y : nat) : dec (x <= y) := le_dec x y.
Arguments size_recursion {X} sigma {p} _ _.
Section Iteration.
Variables (X: Type) (f: X -> X).
Fixpoint it (n : nat) (x : X) : X := match n with | 0 => x | S n' => f (it n' x) end.
Definition FP (x : X) : Prop := f x = x.
End Iteration.

Lemma size_recursion (X : Type) (sigma : X -> nat) (p : X -> Type) : (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> forall x, p x.
Proof.
intros D x.
apply D.
revert x.
enough (forall n y, sigma y < n -> p y) by eauto.
intros n.
induction n; intros y E.
-
exfalso; lia.
-
apply D.
intros x F.
apply IHn.
lia.
