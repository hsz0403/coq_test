Require Import PeanoNat Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments measure_ind {X}.
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma pow_5_mod_2 (n: nat) : 5 ^ n mod 2 = 1.
Proof.
elim: n; first by (cbv; lia).
move=> n IH.
rewrite Nat.pow_succ_r' Nat.mul_mod ?IH; first by lia.
by cbv; lia.
