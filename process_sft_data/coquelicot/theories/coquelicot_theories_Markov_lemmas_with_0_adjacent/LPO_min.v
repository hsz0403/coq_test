Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Theorem LPO_min : forall P : nat -> Prop, (forall n, P n \/ ~ P n) -> {n : nat | P n /\ forall i, (i < n)%nat -> ~ P i} + {forall n, ~ P n}.
Proof.
assert (Hi: forall n, 0 < INR n + 1).
intros N.
rewrite <- S_INR.
apply lt_0_INR.
apply lt_0_Sn.
intros P HP.
set (E y := exists n, (P n /\ y = / (INR n + 1)) \/ (~ P n /\ y = 0)).
assert (HE: forall n, P n -> E (/ (INR n + 1))).
intros n Pn.
exists n.
left.
now split.
assert (BE: is_upper_bound E 1).
intros x [y [[_ ->]|[_ ->]]].
rewrite <- Rinv_1 at 2.
apply Rinv_le_contravar.
exact Rlt_0_1.
rewrite <- S_INR.
apply (le_INR 1), le_n_S, le_0_n.
exact Rle_0_1.
destruct (completeness E) as [l [ub lub]].
now exists 1.
destruct (HP O) as [H0|H0].
exists 1.
exists O.
left.
apply (conj H0).
rewrite Rplus_0_l.
apply sym_eq, Rinv_1.
exists 0.
exists O.
right.
now split.
destruct (Rle_lt_dec l 0) as [Hl|Hl].
right.
intros n Pn.
apply Rle_not_lt with (1 := Hl).
apply Rlt_le_trans with (/ (INR n + 1)).
now apply Rinv_0_lt_compat.
apply ub.
now apply HE.
left.
set (N := Z.abs_nat (up (/l) - 2)).
exists N.
assert (HN: INR N + 1 = IZR (up (/ l)) - 1).
unfold N.
rewrite INR_IZR_INZ.
rewrite inj_Zabs_nat.
replace (IZR (up (/ l)) - 1) with (IZR (up (/ l) - 2) + 1).
apply (f_equal (fun v => IZR v + 1)).
apply Z.abs_eq.
apply Zle_minus_le_0.
apply (Zlt_le_succ 1).
apply lt_IZR.
apply Rle_lt_trans with (/l).
apply Rmult_le_reg_r with (1 := Hl).
rewrite Rmult_1_l, Rinv_l by now apply Rgt_not_eq.
apply lub.
exact BE.
apply archimed.
rewrite minus_IZR.
simpl.
ring.
assert (H: forall i, (i < N)%nat -> ~ P i).
intros i HiN Pi.
unfold is_upper_bound in ub.
refine (Rle_not_lt _ _ (ub (/ (INR i + 1)) _) _).
now apply HE.
rewrite <- (Rinv_involutive l) by now apply Rgt_not_eq.
apply Rinv_1_lt_contravar.
rewrite <- S_INR.
apply (le_INR 1).
apply le_n_S.
apply le_0_n.
apply Rlt_le_trans with (INR N + 1).
apply Rplus_lt_compat_r.
now apply lt_INR.
rewrite HN.
apply Rplus_le_reg_r with (-/l + 1).
ring_simplify.
apply archimed.
destruct (HP N) as [PN|PN].
now split.
elimtype False.
refine (Rle_not_lt _ _ (lub (/ (INR (S N) + 1)) _) _).
intros x [y [[Py ->]|[_ ->]]].
destruct (eq_nat_dec y N) as [HyN|HyN].
elim PN.
now rewrite <- HyN.
apply Rinv_le_contravar.
apply Hi.
apply Rplus_le_compat_r.
apply Rnot_lt_le.
intros Hy.
refine (H _ _ Py).
apply INR_lt in Hy.
clear -Hy HyN.
omega.
now apply Rlt_le, Rinv_0_lt_compat.
rewrite S_INR, HN.
ring_simplify (IZR (up (/ l)) - 1 + 1).
rewrite <- (Rinv_involutive l) at 2 by now apply Rgt_not_eq.
apply Rinv_1_lt_contravar.
rewrite <- Rinv_1.
apply Rinv_le_contravar.
exact Hl.
now apply lub.
apply archimed.
