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

Lemma filterlim_Rabs (x : Rbar) : filterlim Rabs (Rbar_locally' x) (Rbar_locally (Rbar_abs x)).
Proof.
destruct x as [x| | ] => //=.
eapply filterlim_filter_le_1, continuous_Rabs.
intros P [d HP] ; exists d => y Hy _.
by apply HP.
eapply filterlim_ext_loc.
exists 0 => y Hy.
rewrite Rabs_pos_eq // ; by apply Rlt_le.
apply is_lim_id.
eapply filterlim_ext_loc.
exists 0 => y Hy.
rewrite -Rabs_Ropp Rabs_pos_eq // -Ropp_0 ; by apply Ropp_le_contravar, Rlt_le.
apply (is_lim_opp id m_infty m_infty), is_lim_id.
