From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import EqDec.
Instance nat_le_dec (x y : nat) : dec (x <= y) := le_dec x y.
Arguments size_recursion {X} sigma {p} _ _.
Section Iteration.
Variables (X: Type) (f: X -> X).
Fixpoint it (n : nat) (x : X) : X := match n with | 0 => x | S n' => f (it n' x) end.
Definition FP (x : X) : Prop := f x = x.
End Iteration.

Lemma size_induction X (f : X -> nat) (p : X -> Prop) : (forall x, (forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof.
intros IH x.
apply IH.
assert (G: forall n y, f y < n -> p y).
{
intros n.
induction n.
-
intros y B.
exfalso.
lia.
-
intros y B.
apply IH.
intros z C.
apply IHn.
lia.
}
apply G.
