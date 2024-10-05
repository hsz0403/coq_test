Require Import Arith Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma transition_le_gt (f: nat -> nat) (x n1 n2: nat): n1 <= n2 -> f n1 <= x -> x < f n2 -> exists n, n < n2 /\ f n <= x /\ x < f (1+n).
Proof.
move Hk: (n2 - n1) => k.
elim: k n1 n2 Hk.
{
move=> n1 n2 ? ?.
have -> : n1 = n2 by lia.
by lia.
}
move=> k IH n1 [|n2] ? ?; first by lia.
have : f n2 <= x \/ x < f n2 by lia.
case.
-
move=> *.
exists n2.
by constructor.
-
move=> ? ? _.
have [n [? ?]] := (IH n1 n2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
exists n.
by constructor; [lia |].
