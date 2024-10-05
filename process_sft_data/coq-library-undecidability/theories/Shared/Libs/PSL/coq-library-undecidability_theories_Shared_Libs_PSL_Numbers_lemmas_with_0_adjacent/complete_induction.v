From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import EqDec.
Instance nat_le_dec (x y : nat) : dec (x <= y) := le_dec x y.
Arguments size_recursion {X} sigma {p} _ _.
Section Iteration.
Variables (X: Type) (f: X -> X).
Fixpoint it (n : nat) (x : X) : X := match n with | 0 => x | S n' => f (it n' x) end.
Definition FP (x : X) : Prop := f x = x.
End Iteration.

Lemma complete_induction (p : nat -> Prop) (x : nat) : (forall x, (forall y, y<x -> p y) -> p x) -> p x.
Proof.
intros A.
apply A.
induction x ; intros y B.
exfalso ; lia.
apply A.
intros z C.
apply IHx.
lia.
