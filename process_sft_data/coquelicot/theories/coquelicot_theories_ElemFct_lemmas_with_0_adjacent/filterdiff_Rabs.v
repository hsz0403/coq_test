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

Lemma filterdiff_Rabs (x : R) : x <> 0 -> filterdiff Rabs (locally x) (fun y : R => scal y (sign x)).
Proof.
rewrite -/(is_derive Rabs x (sign x)).
move => Hx0.
case: (Rle_lt_dec 0 x) => Hx.
case: Hx => //= Hx.
rewrite sign_eq_1 //.
eapply is_derive_ext_loc.
apply locally_interval with 0 p_infty.
by [].
by [].
move => /= y Hy _.
rewrite Rabs_pos_eq //.
by apply Rlt_le.
by apply @is_derive_id.
by apply sym_eq in Hx.
rewrite sign_eq_m1 //.
eapply is_derive_ext_loc.
apply locally_interval with m_infty 0.
by [].
by [].
move => /= y _ Hy.
rewrite -Rabs_Ropp Rabs_pos_eq //.
rewrite -Ropp_0 ; by apply Rlt_le, Ropp_lt_contravar.
apply @is_derive_opp.
by apply @is_derive_id.
