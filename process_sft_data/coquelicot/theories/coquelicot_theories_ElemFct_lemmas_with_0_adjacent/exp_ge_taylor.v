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

Lemma exp_ge_taylor (x : R) (n : nat) : 0 <= x -> sum_f_R0 (fun k => x^k / INR (fact k)) n <= exp x.
Proof.
move => Hx.
rewrite /exp /exist_exp.
case: Alembert_C3 => /= y Hy.
apply Rnot_lt_le => H.
apply Rminus_lt_0 in H.
case: (Hy _ H) => N {Hy} Hy.
move: (Hy _ (le_plus_r n N)) => {Hy}.
apply Rle_not_lt.
apply Rle_trans with (2 := Rle_abs _).
apply Rplus_le_compat_r.
elim: N => [ | N IH].
rewrite plus_0_r.
apply Req_le.
elim: (n) => {n H} [ | n /= <-].
apply Rmult_comm.
apply f_equal.
apply Rmult_comm.
apply Rle_trans with (1 := IH).
rewrite -plus_n_Sm.
move: (n + N)%nat => {n H N IH} n.
rewrite /sum_f_R0 -/sum_f_R0.
apply Rminus_le_0 ; ring_simplify.
apply Rmult_le_pos.
apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
by apply pow_le.
