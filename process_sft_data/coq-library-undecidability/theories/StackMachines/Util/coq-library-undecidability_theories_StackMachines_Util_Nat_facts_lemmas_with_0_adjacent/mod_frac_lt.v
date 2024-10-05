Require Import Arith Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma mod_frac_lt {n m: nat} : (S m) mod (n + 1) = 0 -> S m < (S m * (n + 2)) / (n + 1).
Proof.
move /Nat.mod_divide => /(_ ltac:(lia)).
move /Nat.divide_div_mul_exact => /(_ _ ltac:(lia)) => H.
have -> : (S m * (n + 2)) = ((1 + (n + 1)) * S m) by lia.
rewrite H /=.
rewrite -(H (n+1)).
have -> : (n + 1) * S m = S m * (n + 1) by lia.
rewrite Nat.div_mul; first by lia.
suff: S m <> S m / (n + 1) + S m by lia.
move /(f_equal (fun x => (n+1) * x)).
rewrite Nat.mul_add_distr_l -(H (n+1)).
have -> : (n + 1) * S m = S m * (n + 1) by lia.
rewrite Nat.div_mul; first by lia.
by lia.
