Require Import Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils_tac utils_nat gcd sums pos vec.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation power := (mscal mult 1).
Section div_mult.
Variable (p q : nat) (Hp : p <> 0) (Hq : q <> 0).
Fact div_rem_mult n : div n (p*q) = div (div n p) q /\ rem n (p*q) = rem n p + p*rem (div n p) q.
Proof using Hp Hq.
assert (p*q <> 0) as Hpq.
{
intros E; apply mult_is_O in E; lia.
}
apply div_rem_uniq with (p := p*q); auto.
+
generalize (div_rem_spec1 n p) (div_rem_spec1 (div n p) q) (div_rem_spec1 n (p*q)); intros H1 H2 H3.
rewrite <- H3; rewrite H1 at 1; rewrite H2 at 1; ring.
+
apply div_rem_spec2; auto.
+
generalize (div_rem_spec2 n Hp) (div_rem_spec2 (div n p) Hq); intros H1 H2.
replace q with (1+(q-1)) at 2 by lia.
rewrite Nat.mul_add_distr_l.
apply plus_lt_le_compat; try lia.
apply mult_le_compat; lia.
End div_mult.
Section nat_nat2_bij.
Let decomp_recomp_full n : n <> 0 -> { a & { b | n = power a 2 * (2*b+1) } }.
Proof.
induction on n as IHn with measure n; intros Hn.
generalize (euclid_2_div n); intros (H1 & H2).
case_eq (rem n 2).
+
intros H.
destruct (IHn (div n 2)) as (a & b & H3); try lia.
exists (S a), b.
rewrite H1, H, H3, power_S; ring.
+
intros [ | [ | k ] ] Hk; try lia.
exists 0, (div n 2); rewrite power_0.
rewrite H1 at 1; rewrite Hk; ring.
Definition decomp_l n := projT1 (@decomp_recomp_full (S n) (Nat.neq_succ_0 _)).
Definition decomp_r n := proj1_sig (projT2 (@decomp_recomp_full (S n) (Nat.neq_succ_0 _))).
Fact decomp_lr_spec n : S n = power (decomp_l n) 2 * (2 * (decomp_r n) + 1).
Proof.
apply (proj2_sig (projT2 (@decomp_recomp_full (S n) (Nat.neq_succ_0 _)))).
Definition recomp a b := power a 2 * (2*b+1) - 1.
Fact recomp_decomp n : n = recomp (decomp_l n) (decomp_r n).
Proof.
unfold recomp; rewrite <- decomp_lr_spec; lia.
Let power_mult_lt_inj a1 b1 a2 b2 : a1 < a2 -> power a1 2 * (2*b1+1) <> power a2 2 * b2.
Proof.
intros H1 H.
replace a2 with (a1+(S (a2-a1-1))) in H by lia.
rewrite power_plus in H.
rewrite <- mult_assoc, Nat.mul_cancel_l in H.
2: generalize (power2_gt_0 a1); lia.
revert H; rewrite power_S, <- mult_assoc.
generalize (power (a2-a1-1) 2*b1); intros; lia.
Let comp_gt a b : power a 2 *(2*b+1) <> 0.
Proof.
intros E; apply mult_is_O in E.
generalize (power2_gt_0 a); intros; lia.
Fact decomp_uniq a1 b1 a2 b2 : power a1 2 * (2*b1+1) = power a2 2 * (2*b2+1) -> a1 = a2 /\ b1 = b2.
Proof.
intros H.
destruct (lt_eq_lt_dec a1 a2) as [ [ H1 | H1 ] | H1 ].
+
exfalso; revert H; apply power_mult_lt_inj; auto.
+
split; auto; subst a2.
rewrite Nat.mul_cancel_l in H; try lia.
generalize (power2_gt_0 a1); lia.
+
exfalso; symmetry in H.
revert H; apply power_mult_lt_inj; auto.
Let decomp_lr_recomp a b : decomp_l (recomp a b) = a /\ decomp_r (recomp a b) = b.
Proof.
apply decomp_uniq; symmetry.
replace (power a 2 * (2*b+1)) with (S (recomp a b)).
+
apply decomp_lr_spec.
+
unfold recomp; generalize (power a 2 * (2*b+1)) (comp_gt a b); intros; lia.
Fact decomp_l_recomp a b : decomp_l (recomp a b) = a.
Proof.
apply decomp_lr_recomp.
Fact decomp_r_recomp a b : decomp_r (recomp a b) = b.
Proof.
apply decomp_lr_recomp.
End nat_nat2_bij.
Fixpoint inject n (v : vec nat n) : nat := match v with | vec_nil => 0 | x##v => recomp x (inject v) end.
Fixpoint project n : nat -> vec nat n := match n with | 0 => fun _ => vec_nil | S n => fun x => decomp_l x ## project _ (decomp_r x) end.
Fact project_inject n v : project _ (@inject n v) = v.
Proof.
induction v as [ | n x v IHv ]; simpl; auto.
rewrite decomp_l_recomp, decomp_r_recomp; f_equal; trivial.

Corollary div_mult n : div n (p*q) = div (div n p) q.
Proof using Hp Hq.
Admitted.

Corollary rem_mult n : rem n (p*q) = rem n p + p*rem (div n p) q.
Proof using Hp Hq.
Admitted.

Let decomp_recomp_full n : n <> 0 -> { a & { b | n = power a 2 * (2*b+1) } }.
Proof.
induction on n as IHn with measure n; intros Hn.
generalize (euclid_2_div n); intros (H1 & H2).
case_eq (rem n 2).
+
intros H.
destruct (IHn (div n 2)) as (a & b & H3); try lia.
exists (S a), b.
rewrite H1, H, H3, power_S; ring.
+
intros [ | [ | k ] ] Hk; try lia.
exists 0, (div n 2); rewrite power_0.
Admitted.

Fact decomp_lr_spec n : S n = power (decomp_l n) 2 * (2 * (decomp_r n) + 1).
Proof.
Admitted.

Fact recomp_decomp n : n = recomp (decomp_l n) (decomp_r n).
Proof.
Admitted.

Let power_mult_lt_inj a1 b1 a2 b2 : a1 < a2 -> power a1 2 * (2*b1+1) <> power a2 2 * b2.
Proof.
intros H1 H.
replace a2 with (a1+(S (a2-a1-1))) in H by lia.
rewrite power_plus in H.
rewrite <- mult_assoc, Nat.mul_cancel_l in H.
2: generalize (power2_gt_0 a1); lia.
revert H; rewrite power_S, <- mult_assoc.
Admitted.

Let comp_gt a b : power a 2 *(2*b+1) <> 0.
Proof.
intros E; apply mult_is_O in E.
Admitted.

Fact decomp_uniq a1 b1 a2 b2 : power a1 2 * (2*b1+1) = power a2 2 * (2*b2+1) -> a1 = a2 /\ b1 = b2.
Proof.
intros H.
destruct (lt_eq_lt_dec a1 a2) as [ [ H1 | H1 ] | H1 ].
+
exfalso; revert H; apply power_mult_lt_inj; auto.
+
split; auto; subst a2.
rewrite Nat.mul_cancel_l in H; try lia.
generalize (power2_gt_0 a1); lia.
+
exfalso; symmetry in H.
Admitted.

Let decomp_lr_recomp a b : decomp_l (recomp a b) = a /\ decomp_r (recomp a b) = b.
Proof.
apply decomp_uniq; symmetry.
replace (power a 2 * (2*b+1)) with (S (recomp a b)).
+
apply decomp_lr_spec.
+
Admitted.

Fact decomp_l_recomp a b : decomp_l (recomp a b) = a.
Proof.
Admitted.

Fact project_inject n v : project _ (@inject n v) = v.
Proof.
induction v as [ | n x v IHv ]; simpl; auto.
Admitted.

Fact decomp_r_recomp a b : decomp_r (recomp a b) = b.
Proof.
apply decomp_lr_recomp.
