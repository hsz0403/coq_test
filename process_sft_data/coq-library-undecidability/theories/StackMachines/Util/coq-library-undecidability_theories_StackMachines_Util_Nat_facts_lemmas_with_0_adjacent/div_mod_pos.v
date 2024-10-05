Require Import Arith Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma div_mod_pos {n m: nat} : S m / (1 + n) + S m mod (1 + n) <> 0.
Proof.
move=> ?.
have /Nat.div_small_iff : S m / (1 + n) = 0 by lia.
move /(_ ltac:(lia)).
have /Nat.div_exact : S m mod (1 + n) = 0 by lia.
move /(_ ltac:(lia)).
by lia.
