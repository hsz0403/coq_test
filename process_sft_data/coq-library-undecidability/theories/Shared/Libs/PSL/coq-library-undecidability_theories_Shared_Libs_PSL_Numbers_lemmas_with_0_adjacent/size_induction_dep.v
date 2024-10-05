From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import EqDec.
Instance nat_le_dec (x y : nat) : dec (x <= y) := le_dec x y.
Arguments size_recursion {X} sigma {p} _ _.
Section Iteration.
Variables (X: Type) (f: X -> X).
Fixpoint it (n : nat) (x : X) : X := match n with | 0 => x | S n' => f (it n' x) end.
Definition FP (x : X) : Prop := f x = x.
End Iteration.

Lemma size_induction_dep L (X : L -> Type) (f : forall l, X l -> nat) (p : forall l, X l -> Type) : (forall l x, (forall l' y, f l' y < f l x -> p l' y) -> p l x) -> forall l x, p l x.
Proof.
intros IH l x.
apply IH.
intros l'.
assert (G: forall n l' y, f l' y < n -> p l' y).
{
intros n.
induction n; intros l'' y.
-
intros B.
exfalso.
lia.
-
intros B.
apply IH.
intros ll z C.
eapply IHn.
lia.
}
apply G.
