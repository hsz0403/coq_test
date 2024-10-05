From Undecidability.Shared.Libs.PSL Require Import Prelim.
From Undecidability.Shared.Libs.PSL Require Import EqDec.
Instance nat_le_dec (x y : nat) : dec (x <= y) := le_dec x y.
Arguments size_recursion {X} sigma {p} _ _.
Section Iteration.
Variables (X: Type) (f: X -> X).
Fixpoint it (n : nat) (x : X) : X := match n with | 0 => x | S n' => f (it n' x) end.
Definition FP (x : X) : Prop := f x = x.
End Iteration.

Lemma it_fp (sigma : X -> nat) x : (forall n, FP (it n x) \/ sigma (it n x) > sigma (it (S n) x)) -> FP (it (sigma x) x).
Proof.
intros A.
assert (B: forall n, FP (it n x) \/ sigma x >= n + sigma (it n x)).
{
intros n; induction n; cbn.
-
auto.
-
destruct IHn as [B|B].
+
left.
now rewrite B.
+
destruct (A n) as [C|C].
*
left.
now rewrite C.
*
right.
cbn in C.
lia.
}
destruct (A (sigma x)), (B (sigma x)); auto; exfalso; lia.
