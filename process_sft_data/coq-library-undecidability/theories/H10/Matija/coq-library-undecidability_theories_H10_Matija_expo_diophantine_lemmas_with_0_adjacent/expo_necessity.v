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

Lemma expo_necessity : expo_conditions -> p = expo r q.
Proof.
unfold expo_conditions.
intros [ (H1 & H2) | [ (H1 & H2 & H3) | ((H0 & H1) & b & m & a1 & a2 & a3 & (_ & H2) & (H3 & H4) & (H5 & H6) & H7 & H8 & H9 & H10) ] ].
+
subst; auto.
+
subst; rewrite power_of_0; auto.
+
assert (m = b*q - q*q -1) as Hm1 by lia.
assert (m <> 0) as Hm by lia.
assert (q*q+2 <= q*q*q+2*q) as Hq'.
{
apply H_q3_q; lia.
}
assert (expo r q < m) as Hq.
{
rewrite Hm1, H7.
do 2 rewrite Nat.mul_add_distr_r.
apply lt_le_trans with (a1*1+1).
+
rewrite plus_comm, Nat.mul_1_r; apply le_n_S.
destruct alpha_nat_power with (b_nat := q+4) (n := r) as (G1 & _); try lia.
rewrite H2.
apply le_trans with (2 := G1), power_mono_r; lia.
+
rewrite <- Nat.sub_add_distr, <- plus_assoc, <- Nat.add_sub_assoc; try lia.
apply plus_le_compat; try lia.
apply mult_le_compat; lia.
}
rewrite <- (rem_lt Hm H9), <- (rem_lt Hm Hq).
revert H10.
rewrite Hm1 in Hm |- *.
do 2 rewrite <- nat2Zp_inj with (Hp := Hm).
do 2 rewrite nat2Zp_plus.
rewrite H4, expo_congruence; auto; [ | lia ].
rewrite H6, nat2Zp_plus.
destruct r as [ | r' ]; [ lia | ].
replace (S r' -1) with r' by lia.
simpl plus.
rewrite alpha_nat_fix_2, nat2Zp_minus.
2: apply alpha_nat_le; lia.
intros H; rewrite Zp_opp_plus_eq in H.
rewrite H.
rewrite (Zp_plus_comm _ 〚b * _〛 (∸ _)).
repeat rewrite <- Zp_plus_assoc.
rewrite Zp_minus, Zp_plus_zero_r.
rewrite Zp_plus_comm, <- Zp_plus_assoc.
rewrite (Zp_plus_comm _ (∸ _)), Zp_minus, Zp_plus_zero_r.
trivial.
