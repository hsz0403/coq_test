Require Import Arith Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma divides_frac_diff {m n} : m mod (n + 1) = 0 -> (m * (n + 2) / (n + 1) - m) * (1 + n) = m.
Proof.
rewrite Nat.mul_sub_distr_r.
move=> /Nat.div_exact => /(_ ltac:(lia)) ?.
have -> : m * (n + 2) = ((n+2) * (m / (n + 1))) * (n + 1) by lia.
by rewrite Nat.div_mul; lia.
