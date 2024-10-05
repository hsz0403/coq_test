Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive RInt Continuity Lim_seq ElemFct RInt_analysis.
Ltac pos_rat := repeat ( apply Rdiv_lt_0_compat || apply Rplus_lt_0_compat || apply Rmult_lt_0_compat) ; try by apply Rlt_0_1.
Definition fab (a b x : R) : R := (a + b * ln x) / x.
Definition f (x : R) : R := fab 2 2 x.
Fixpoint u (n : nat) : R := match n with | O => 2 | S n => 2/3 * u n + 1/3 * (INR n) + 1 end.
Definition v (n : nat) : R := u n - INR n.
Definition Su (n : nat) : R := sum_f_R0 u n.
Definition Tu (n : nat) : R := Su n / (INR n) ^ 2.

Lemma f_eq_1_0_1 : exists x, 0 < x <= 1 /\ f x = 1.
Proof.
case: (IVT_Rbar_incr (fun x => f (Rabs x)) 0 1 m_infty 2 1).
eapply filterlim_comp.
apply filterlim_Rabs_0.
by apply filterlim_f_0.
apply is_lim_comp with 1.
replace 2 with (f 1).
apply is_lim_continuity.
apply derivable_continuous_pt.
exists (((2 - 2) - 2 * ln 1) / 1 ^ 2) ; apply is_derive_Reals, Dfab.
by apply Rlt_0_1.
rewrite /f /fab ln_1 /= ; field.
rewrite -{2}(Rabs_pos_eq 1).
apply (is_lim_continuity Rabs 1).
by apply continuity_pt_filterlim, continuous_Rabs.
by apply Rle_0_1.
exists (mkposreal _ Rlt_0_1) => /= x H0x Hx.
rewrite /ball /= /AbsRing_ball /= in H0x.
apply Rabs_lt_between' in H0x.
rewrite Rminus_eq_0 in H0x.
contradict Hx.
rewrite -(Rabs_pos_eq x).
by apply Rbar_finite_eq.
by apply Rlt_le, H0x.
move => x H0x Hx1.
apply (continuity_pt_comp Rabs).
by apply continuity_pt_filterlim, continuous_Rabs.
rewrite Rabs_pos_eq.
apply derivable_continuous_pt.
exists (((2 - 2) - 2 * ln x) / x ^ 2) ; apply is_derive_Reals, Dfab.
by [].
by apply Rlt_le.
by apply Rlt_0_1.
split => //.
apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
move => x [H0x [Hx1 Hfx]].
rewrite Rabs_pos_eq in Hfx.
exists x ; repeat split.
by apply H0x.
by apply Rlt_le.
by apply Hfx.
by apply Rlt_le.
