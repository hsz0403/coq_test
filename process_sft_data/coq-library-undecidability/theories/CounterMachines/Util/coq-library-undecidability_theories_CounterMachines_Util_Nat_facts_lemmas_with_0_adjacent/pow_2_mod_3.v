Require Import PeanoNat Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments measure_ind {X}.
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma pow_2_mod_3 (n: nat) : 2 ^ n mod 3 = 1 \/ 2 ^ n mod 3 = 2.
Proof.
elim: n; first by (cbv; lia).
move=> n IH.
rewrite Nat.pow_succ_r' Nat.mul_mod; first by lia.
move: IH => [->|->]; cbv; by lia.
