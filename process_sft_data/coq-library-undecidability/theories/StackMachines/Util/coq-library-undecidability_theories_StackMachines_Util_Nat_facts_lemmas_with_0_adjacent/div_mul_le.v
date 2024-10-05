Require Import Arith Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma div_mul_le m n : n <> 0 -> (m / n) * n <= m.
Proof.
move=> ?.
have := Nat.div_mod m n ltac:(lia).
by lia.
