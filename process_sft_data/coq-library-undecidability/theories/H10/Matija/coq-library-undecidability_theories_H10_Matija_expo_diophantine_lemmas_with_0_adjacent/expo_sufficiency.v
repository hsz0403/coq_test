Require Import Arith ZArith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd sums.
From Undecidability.H10.ArithLibs Require Import Zp.
From Undecidability.H10.Matija Require Import alpha.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation expo := (mscal mult 1).
Section expo_diophantine.
Variables (p q r : nat).
Definition expo_conditions := r = 0 /\ p = 1 \/ q = 0 /\ 0 < r /\ p = 0 \/ (0 < r /\ q <> 0) /\ exists b m a1 a2 a3, (3 < q+4 /\ a1 = alpha_nat (q+4) (1+r)) /\ (3 < b /\ a2 = alpha_nat b r) /\ (3 < b /\ a3 = alpha_nat b (1+r)) /\ b = a1+q*q+2 /\ m + q*q + 1 = b*q /\ p < m /\ rem (p+b*a2) m = rem (q*a2+a3) m.
Let H_q3_q : 0 < q -> q*q+2 <= q*q*q+2*q.
Proof.
intros H.
apply plus_le_compat; try lia.
replace q with (1+(q-1)) at 3 by lia.
rewrite <- mult_assoc, Nat.mul_add_distr_r, Nat.mul_1_l.
apply le_plus_l.
Infix "⊕" := (Zp_plus _) (at level 50, left associativity).
Infix "⊗" := (Zp_mult _) (at level 40, left associativity).
Notation "∸" := (Zp_opp _).
Notation f := (nat2Zp _).
Notation "〚 x 〛" := (f x).
Ltac fold_nat2Zp := repeat match goal with | |- context[nat2Zp _ ?x ⊕ nat2Zp _ ?y] => rewrite <- nat2Zp_plus | |- context[nat2Zp _ ?x ⊗ nat2Zp _ ?y] => rewrite <- nat2Zp_mult | |- context[∸ nat2Zp _ ?x] => fail end.
End expo_diophantine.
Local Hint Resolve expo_sufficiency expo_necessity : core.

Lemma expo_sufficiency : p = expo r q -> expo_conditions.
Proof.
intros H.
destruct (le_lt_dec r 0) as [ Hr | Hr ]; red.
1: {
left; revert H; replace r with 0 by lia; rewrite mscal_0; tauto.
}
destruct (eq_nat_dec q 0) as [ Hq | Hq ].
1: {
right; left; subst; rewrite power_of_0; auto.
}
remember (alpha_nat (q+4) (S r)) as a1.
remember (a1+q*q+2) as b.
remember (alpha_nat b r) as a2.
remember (alpha_nat b (1+r)) as a3.
remember (b*q-q*q-1) as m.
right; right; split; auto; exists b, m, a1, a2, a3.
assert (3 < b) as Hb.
{
rewrite Heqb.
apply lt_le_trans with (1+(1*1)+2); try lia.
repeat apply plus_le_compat; auto.
+
rewrite Heqa1.
apply alpha_nat_mono with (i := 1); lia.
+
apply mult_le_compat; lia.
}
assert (2 <= b) as Hb' by lia.
destruct (@alpha_nat_power (q+4)) with (n := r) as (H1 & H2); try lia.
assert (q*q+2 <= q*q*q+2*q) as Hq'.
{
apply H_q3_q; lia.
}
assert (m <> 0) as Hm.
{
rewrite Heqm, Heqb.
do 2 rewrite Nat.mul_add_distr_r.
assert (a1*q <> 0) as Ha1.
{
intros E; apply mult_is_O in E.
destruct E as [ E | ]; try lia.
revert E; rewrite Heqa1.
apply alpha_nat_gt_0; lia.
}
revert Ha1; generalize (a1*q); intros x Hx.
lia.
}
assert (expo r q < m) as Hexpo.
{
rewrite Heqm, Heqb.
do 2 rewrite Nat.mul_add_distr_r.
rewrite <- Heqa1 in H1.
apply lt_le_trans with (a1*1+1).
+
rewrite plus_comm, Nat.mul_1_r; apply le_n_S.
apply le_trans with (2 := H1).
apply power_mono_r; lia.
+
rewrite <- Nat.sub_add_distr, <- plus_assoc, <- Nat.add_sub_assoc; try lia.
apply plus_le_compat; try lia.
apply mult_le_compat; lia.
}
repeat (split; auto); try lia.
rewrite <- nat2Zp_inj with (Hp := Hm).
do 2 rewrite nat2Zp_plus.
rewrite Heqa2.
revert Hm; rewrite Heqm; intros Hm.
rewrite expo_congruence; auto.
rewrite <- H, plus_comm, nat2Zp_plus, <- Zp_plus_assoc; f_equal.
rewrite <- nat2Zp_plus; f_equal.
rewrite Heqa3.
destruct r as [ | r' ]; try lia.
replace (S r' -1) with r' by lia.
simpl plus at 2.
rewrite alpha_nat_fix_2.
generalize (alpha_nat_le Hb' r'); lia.
