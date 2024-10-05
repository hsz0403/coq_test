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

Lemma continuous_abs {K : AbsRing} (x : K) : continuous abs x.
Proof.
apply filterlim_locally => /= eps.
exists eps => /= y Hy.
eapply Rle_lt_trans, Hy.
wlog: x y Hy / (abs x <= abs y) => [Hw | Hxy].
case: (Rle_lt_dec (abs x) (abs y)) => Hxy.
by apply Hw.
rewrite abs_minus (abs_minus y).
apply Hw, Rlt_le, Hxy.
by apply ball_sym.
rewrite {1}/abs /=.
rewrite Rabs_pos_eq.
apply Rle_minus_l.
eapply Rle_trans, abs_triangle.
apply Req_le, f_equal.
by rewrite /minus -plus_assoc plus_opp_l plus_zero_r.
by apply -> Rminus_le_0.
