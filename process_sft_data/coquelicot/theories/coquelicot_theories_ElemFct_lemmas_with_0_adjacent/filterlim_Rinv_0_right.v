Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.
Section nat_to_ring.
Context {K : Ring}.
Definition nat_to_ring (n : nat) : K := sum_n_m (fun _ => one) 1 n.
End nat_to_ring.
Section is_derive_mult.
Context {K : AbsRing}.
End is_derive_mult.

Lemma filterlim_Rinv_0_right : filterlim Rinv (at_right 0) (Rbar_locally p_infty).
Proof.
intros P [M HM].
have Hd : 0 < / Rmax 1 M.
apply Rinv_0_lt_compat.
apply Rlt_le_trans with (2 := Rmax_l _ _).
by apply Rlt_0_1.
exists (mkposreal _ Hd) => x /= Hx Hx0.
apply HM.
apply Rle_lt_trans with (1 := Rmax_r 1 M).
replace (Rmax 1 M) with (/ / Rmax 1 M) by (field ; apply Rgt_not_eq, Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1).
apply Rinv_lt_contravar.
apply Rdiv_lt_0_compat with (1 := Hx0).
apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /= in Hx.
rewrite -/(Rminus _ _) Rminus_0_r Rabs_pos_eq // in Hx.
exact: Rlt_le.
