Require Import PeanoNat Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments measure_ind {X}.
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma mod_frac_neq {n m: nat} : S m mod (n + 1) = 0 -> (S m * (n + 2)) / (n + 1) <> S m.
Proof.
move /mod_frac_lt.
by lia.
