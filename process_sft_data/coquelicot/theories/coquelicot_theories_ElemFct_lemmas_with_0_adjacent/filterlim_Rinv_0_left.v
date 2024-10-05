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

Lemma filterlim_Rinv_0_left : filterlim Rinv (at_left 0) (Rbar_locally m_infty).
Proof.
eapply filterlim_ext_loc.
exists (mkposreal _ Rlt_0_1) => /= y _ Hy0.
rewrite -{2}(Ropp_involutive y).
rewrite -Ropp_inv_permute.
reflexivity.
contradict Hy0.
apply Rle_not_lt, Req_le.
by rewrite -(Ropp_involutive y) Hy0 Ropp_0.
eapply filterlim_comp.
eapply filterlim_comp.
by apply filterlim_Ropp_left.
rewrite Ropp_0.
by apply filterlim_Rinv_0_right.
apply filterlim_Rbar_opp.
