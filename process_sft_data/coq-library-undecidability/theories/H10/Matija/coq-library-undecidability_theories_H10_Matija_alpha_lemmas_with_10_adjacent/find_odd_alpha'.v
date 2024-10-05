Require Import Arith Lia ZArith.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd prime crt binomial sums.
From Undecidability.H10.ArithLibs Require Import matrix Zp.
Set Default Proof Using "Type".
Set Implicit Arguments.
Section Zp_alpha_2.
Variable (ak am k l m : nat) (H1 : m = (l*k)%nat) (H2 : (ak*ak <> 0)%nat).
Notation "〚 u 〛" := (nat2Zp H2 u).
Infix "⊗" := (Zp_mult H2) (at level 40, left associativity).
Hypothesis (H3 : (m <> 0)%nat) (H4 : exists q, Zp_invertible H2 q /\〚am〛 = q⊗〚l〛⊗〚ak〛).
Let Hak : ak <> 0.
Proof.
intro; subst; destruct H2; auto.
Let Hl : l <> 0.
Proof.
contradict H3; subst; ring.
Let Hk : k <> 0.
Proof.
contradict H3; subst; ring.
End Zp_alpha_2.
Local Infix "│" := divides (at level 70, no associativity).
Section Pell.
Variable (b_nat : nat) (Hb_nat : 2 <= b_nat).
Fixpoint alpha_nat n := match n with | 0 => 0 | S p => match p with | 0 => 1 | S r => b_nat * alpha_nat p - alpha_nat r end end.
Fact alpha_nat_fix_0 : alpha_nat 0 = 0.
Proof.
auto.
Fact alpha_nat_fix_1 : alpha_nat 1 = 1.
Proof.
auto.
Fact alpha_nat_fix_2 n : alpha_nat (S (S n)) = b_nat *alpha_nat (S n) - alpha_nat n.
Proof.
auto.
Fact alpha_nat_2 n : b_nat = 2 -> alpha_nat n = n.
Proof using Hb_nat.
intros Hb.
induction on n as IHn with measure n.
destruct n as [ | [ | n ] ]; auto.
rewrite alpha_nat_fix_2, Hb, IHn, IHn; lia.
Fact alpha_nat_inc n : alpha_nat n < alpha_nat (S n).
Proof using Hb_nat.
induction n as [ | n IHn ]; try (simpl; lia).
rewrite alpha_nat_fix_2.
replace b_nat with (2+(b_nat-2)) by lia.
rewrite Nat.mul_add_distr_r.
generalize ((b_nat -2)*alpha_nat (S n)); intro; lia.
Fact alpha_nat_ge_n n : n <= alpha_nat n.
Proof using Hb_nat.
induction n as [ | n IHn ].
+
simpl; auto.
+
apply le_n_S in IHn.
apply le_trans with (1 := IHn), alpha_nat_inc.
Fact alpha_nat_gt_0 : forall n, n <> 0 -> alpha_nat n <> 0.
Proof using Hb_nat.
intros [ | n ] H; try lia.
generalize (alpha_nat_ge_n (S n)); lia.
Fact alpha_nat_le n : alpha_nat n <= b_nat * alpha_nat (S n).
Proof using Hb_nat.
apply le_trans with (1*alpha_nat (S n)).
+
apply lt_le_weak, lt_le_trans with (1 := alpha_nat_inc _); lia.
+
apply mult_le_compat; lia.
Notation power := (mscal mult 1).
Fact alpha_nat_power n : 2 < b_nat -> power n (b_nat-1) <= alpha_nat (S n) <= power n b_nat.
Proof using Hb_nat.
intros Hb.
induction on n as IHn with measure n.
destruct n as [ | [ | n ] ].
+
do 2 rewrite power_0; simpl; lia.
+
do 2 rewrite power_1; simpl; lia.
+
rewrite alpha_nat_fix_2.
destruct (IHn n) as (H1 & H2); try lia.
destruct (IHn (S n)) as (H3 & H4); try lia.
split.
*
replace b_nat with (b_nat-1+1) at 2 by lia.
rewrite Nat.mul_add_distr_r.
rewrite <- (Nat.add_sub_assoc (_*_)).
-
apply le_trans with (2 := le_plus_l _ _).
rewrite power_S; apply mult_le_compat; auto.
-
rewrite Nat.mul_1_l; apply alpha_nat_mono; lia.
*
rewrite power_S.
apply le_trans with (1 := Nat.le_sub_l _ _).
apply mult_le_compat_l; auto.
Open Scope Z.
Let b := Z.of_nat b_nat.
Let Hb : 2 <= b.
Proof.
apply inj_le with (n:= 2%nat); lia.
Definition alpha_Z n := match n with | 0%nat => -1 | S n => Z.of_nat (alpha_nat n) end.
Notation α := alpha_Z.
Hint Resolve alpha_nat_le : core.
Fact alpha_Z_S n : α (S n) = Z.of_nat (alpha_nat n).
Proof.
auto.
Fact alpha_fix_0 : α (0%nat) = -1.
Proof.
auto.
Fact alpha_fix_1 : α 1%nat = 0.
Proof.
auto.
Fact alpha_fix_2 : α 2%nat = 1.
Proof.
auto.
Fact alpha_fix_3 n : α (S (S n)) = b*α (S n) - α n.
Proof using Hb_nat.
destruct n as [ | n ].
1: simpl; ring.
unfold α at 1.
rewrite alpha_nat_fix_2.
rewrite Nat2Z.inj_sub; auto.
rewrite Nat2Z.inj_mul; auto.
Fact alpha_inc n : α n < α (S n).
Proof using Hb_nat.
destruct n; simpl; try lia.
apply inj_lt, alpha_nat_inc.
Fact alpha_ge_0 n : 0 <= α (S n).
Proof using Hb_nat.
induction n as [ | n IHn ].
+
rewrite alpha_fix_1; lia.
+
apply Zlt_le_weak, Z.le_lt_trans with (2 := alpha_inc _); trivial.
Opaque α.
Create HintDb alpha_db.
Hint Rewrite alpha_fix_0 alpha_fix_1 alpha_fix_2 alpha_fix_3 : alpha_db.
Ltac alpha := autorewrite with alpha_db.
Fact alpha_2 : b = 2 -> forall n, α n = Z.of_nat n - 1.
Proof using Hb_nat.
intros H n.
induction on n as IHn with measure n.
destruct n as [ | [ | n ] ]; alpha; auto.
do 2 (rewrite IHn; try lia).
Notation MZ := (M22 Z).
Notation MZ_opp := (MI22 Z.opp).
Notation MZ_plus := (PL22 Zplus).
Notation MZ_mult := (MU22 Zplus Zmult).
Notation MZ_zero := (ZE_22 0).
Notation MZ_one := (ID_22 0 1).
Notation MZ_scal := (M22scal Zmult).
Notation MZ_expo := (mscal MZ_mult MZ_one).
Notation MZ_det := (Det22 Zplus Zmult Z.opp).
Local Fact MZ_plus_monoid : monoid_theory MZ_plus MZ_zero.
Proof.
apply M22plus_monoid with (1 := Zring).
Local Fact MZ_mult_monoid : monoid_theory MZ_mult MZ_one.
Proof.
apply M22mult_monoid with (1 := Zring).
Hint Resolve MZ_plus_monoid MZ_mult_monoid : core.
Section Pell_inner.
Local Notation "⊟" := MZ_opp.
Local Infix "⊞" := MZ_plus (at level 50, left associativity).
Local Infix "⊠" := MZ_mult (at level 40, left associativity).
Definition B : MZ := (b,-1,1,0).
Definition iB : MZ := (0,1,-1,b).
Definition A n := (α (2+n),-α(1+n),α(1+n),-α n).
Definition iA n := (-α n,α(1+n),-α(1+n),α (2+n)).
Notation mI := (-1,0,0,-1).
Fact B_iB : B ⊠ iB = MZ_one.
Proof.
apply M22_equal; ring.
Fact iB_i : iB ⊠ B = MZ_one.
Proof.
apply M22_equal; ring.
Fact A_is_sum k : A k = MZ_scal (-α k) MZ_one ⊞ MZ_scal (α (S k)) B.
Proof using Hb_nat.
simpl; apply M22_equal; simpl; alpha; ring.
Hint Resolve MZ_expo_A : core.
Fact A_plus u v : A (u+v)%nat = A u ⊠ A v.
Proof using Hb_nat.
rewrite <- MZ_expo_A, mscal_plus; auto.
f_equal; auto.
Fact A_mult u v : A (u*v)%nat = MZ_expo u (A v).
Proof using Hb_nat.
rewrite <- MZ_expo_A, mscal_mult; auto.
f_equal; auto.
Fact A_plus_mult m n k l : (m = n + l * k)%nat -> A m = A n ⊠ MZ_expo l (A k).
Proof using Hb_nat.
intro; subst; rewrite A_plus, A_mult; auto.
Fact MZ_det_B : MZ_det B = 1.
Proof.
simpl; ring.
Definition Pell x y := x*x -b*x*y+y*y=1.
Fact A_iA n : A n ⊠ iA n = MZ_one.
Proof using Hb_nat.
generalize (alpha_Pell n); unfold Pell; intros H.
apply M22_equal; try ring; simpl; rewrite alpha_fix_3, <- H; ring.
Fact iA_A n : iA n ⊠ A n = MZ_one.
Proof using Hb_nat.
generalize (alpha_Pell n); unfold Pell; intros H.
apply M22_equal; try ring; simpl; rewrite alpha_fix_3, <- H; ring.
Fact A_minus u v : (v <= u)%nat -> A (u-v)%nat = A u ⊠ iA v.
Proof using Hb_nat.
intros H.
rewrite <- (MZ_expo_A u).
replace u with (u-v+v)%nat at 2 by lia.
rewrite mscal_plus; auto.
do 2 rewrite MZ_expo_A.
rewrite <- M22mult_assoc with (1 := Zring).
rewrite A_iA.
rewrite M22mult_one_r with (1 := Zring).
trivial.
Section alpha_nat_coprime.
Let A_eq_3_12 n : exists u v, u*α (S n) + v*α n = 1.
Proof.
generalize (alpha_Pell n); unfold Pell; intros H.
exists (α (S n)-b*α n), (α n).
rewrite <- H; ring.
End alpha_nat_coprime.
End Pell_inner.
Notation expoZ := (mscal Zmult 1).
Fact expoZ_power n x : expoZ n (Z.of_nat x) = Z.of_nat (power n x).
Proof.
symmetry; apply mscal_morph; auto.
intros; apply Nat2Z.inj_mul.
Fact mscal_Zplus n : mscal Zplus 0 n 1 = Z.of_nat n.
Proof.
induction n as [ | n IHn ].
+
rewrite mscal_0; auto.
+
rewrite mscal_S, IHn.
rewrite Nat2Z.inj_succ; ring.
Notation "∑" := (msum MZ_plus MZ_zero).
Section A2m.
Variable (l m v : nat) (Hv : Z.of_nat v = α (2+m) - α m).
Fact alpha_SSm_m_neq_0 : v <> 0%nat.
Proof using Hb_nat Hv.
intros H; subst; simpl in Hv.
generalize (alpha_inc m) (alpha_inc (S m)); lia.
Notation Hv' := alpha_SSm_m_neq_0.
Let Z2Zp_morph := Z2Zp_morphishm Hv'.
Notation f := (Z2Zp Hv').
Notation "〚 x 〛" := (f x).
Notation "〘 x 〙" := (morph22 f x).
Local Notation "⊟" := (MI22 (Zp_opp Hv')).
Local Infix "⊠" := (MU22 (Zp_plus Hv') (Zp_mult Hv')) (at level 40, left associativity).
Let Am_iAm_mod :〘A m〙= ⊟〘iA m〙.
Proof.
apply M22_equal.
+
rewrite Z2Zp_opp, Zp_opp_inv.
apply Z2Zp_inj.
exists 1; rewrite Hv; ring.
+
rewrite Z2Zp_opp; auto.
+
rewrite Z2Zp_opp, Zp_opp_inv; auto.
+
rewrite <- Z2Zp_opp.
apply Z2Zp_inj.
exists 1; rewrite Hv; ring.
Fact A2m_mod : 〘A (2*m)〙= ⊟〘MZ_one〙.
Proof.
rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A; auto.
rewrite mscal_S, mscal_1; auto.
rewrite MU22_morph with (1 := Z2Zp_morph).
rewrite Am_iAm_mod at 1.
do 2 rewrite <- MI22_morph with (1 := Z2Zp_morph).
rewrite <- MU22_morph with (1 := Z2Zp_morph).
f_equal.
rewrite M22_opp_mult_l with (1 := Zring); f_equal.
apply iA_A.
Fact A2lm_mod : 〘A (2*l*m)〙= 〘MZ_scal (mscal Zmult 1 l (-1)) MZ_one〙.
Proof.
replace (2*l*m)%nat with (l*(2*m))%nat by ring.
rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A; auto.
rewrite expo22_morph with (1 := Z2Zp_morph).
rewrite A2m_mod.
rewrite <- MI22_morph with (1 := Z2Zp_morph).
rewrite <- expo22_morph with (1 := Z2Zp_morph).
f_equal.
rewrite <- M22scal_MI22 with (1 := Zring).
change (-(1)) with (-1).
rewrite expo22_scal with (1 := Zring); f_equal.
rewrite mscal_of_unit; auto.
Let expoZ_opp1 i : expoZ i (-1) = 1 \/ expoZ i (-1) = -1.
Proof.
induction i as [ | i IHi ].
+
rewrite mscal_0; auto.
+
rewrite mscal_S; lia.
Variable (j : nat) (Hl : (l <> 0)%nat) (Hj : (j <= m)%nat).
Fact alpha_2lm_plus_j :〚α (S (2*l*m+j))〛=〚expoZ l (-1)*α (S j)〛.
Proof.
generalize (A_plus (2*l*m) j); intros H.
apply f_equal with (f := morph22 f) in H.
rewrite MU22_morph with (1 := Z2Zp_morph) in H.
rewrite A2lm_mod in H.
rewrite <- MU22_morph with (1 := Z2Zp_morph) in H.
apply M22_proj12 in H.
rewrite Z.mul_0_r, Z.mul_0_l, Z.mul_1_r, Z.add_0_l in H.
apply H.
Let Hj' : (j <= 2*l*m)%nat.
Proof.
apply le_trans with (1*m)%nat; try lia.
apply mult_le_compat; lia.
Fact alpha_2lm_minus_j :〚α (S (2*l*m-j))〛=〚expoZ (S l) (-1)*α (S j)〛.
Proof using Hl Hj.
generalize (A_minus Hj'); intros H.
apply f_equal with (f := morph22 f) in H.
rewrite MU22_morph with (1 := Z2Zp_morph) in H.
rewrite A2lm_mod in H.
rewrite <- MU22_morph with (1 := Z2Zp_morph) in H.
apply M22_proj12 in H.
rewrite Z.mul_0_r, Z.mul_0_l, Z.mul_1_r, Z.add_0_l in H.
unfold plus in H; rewrite H; f_equal.
rewrite mscal_S; ring.
End A2m.
Section expo_congruence.
Variable (q : nat).
Notation m := (b_nat*q-q*q-1)%nat.
Hypothesis Hm : m <> 0%nat.
Let Hq : (1+q*q < b_nat*q)%nat.
Proof.
lia.
Let VP : MZ := (Z.of_nat q,0,1,0).
Notation Zm_ring := (Zp_is_ring Hm).
Add Ring m_ring : Zm_ring.
Notation qz := (Z.of_nat q).
Let Z2Zp_morph := Z2Zp_morphishm Hm.
Infix "⊕" := (Zp_plus Hm) (at level 50, left associativity).
Infix "⊗" := (Zp_mult Hm) (at level 40, left associativity).
Notation "∸" := (Zp_opp Hm).
Notation f := (Z2Zp Hm).
Notation "〚 x 〛" := (f x).
Let qz_eq :〚b〛⊗〚qz〛 ⊕ ∸ (〚qz〛⊗〚qz〛 ⊕〚1〛) = Zp_zero Hm.
Proof.
do 2 rewrite <- Z2Zp_mult.
rewrite <- Z2Zp_plus, <- Z2Zp_opp, <- Z2Zp_plus.
unfold b.
do 2 rewrite <- Nat2Z.inj_mul.
change 1 with (Z.of_nat 1%nat).
rewrite Z.add_opp_r, <- Nat2Z.inj_add, <- Nat2Z.inj_sub; try lia.
rewrite Nat.sub_add_distr; fold m.
rewrite Z2Zp_of_nat, nat2Zp_p; auto.
Notation "〘 x 〙" := (morph22 f x).
Local Infix "⊠" := (MU22 (Zp_plus Hm) (Zp_mult Hm)) (at level 40, left associativity).
Notation scal := (M22scal (Zp_mult Hm)).
Let BVP : 〘 B 〙 ⊠ 〘 VP 〙= scal〚qz〛〘 VP 〙.
Proof.
apply M22_equal; try rewrite Z2Zp_zero; try ring.
change (-1) with (-(1)).
rewrite Z2Zp_opp, Zp_opp_mult, <- (Z2Zp_mult _ 1).
rewrite Z.mul_1_l, <- (Zp_plus_zero Hm), <- qz_eq.
ring.
Let AnVP n :〘 A n 〙 ⊠ 〘 VP 〙= scal〚expoZ n qz〛〘 VP 〙.
Proof.
rewrite <- MZ_expo_A.
induction n as [ | n IHn ].
+
do 2 rewrite mscal_0.
apply M22_equal; try rewrite Z2Zp_zero; try rewrite Z2Zp_one; ring.
+
rewrite mscal_plus1; auto.
rewrite MU22_morph with (1 := Z2Zp_morph).
rewrite <- M22mult_assoc with (1 := Zm_ring).
rewrite BVP.
rewrite <- M22scal_MU22_r with (1 := Zm_ring).
rewrite IHn, mscal_S, M22scal_mult with (1 := Zm_ring).
f_equal.
rewrite Z2Zp_mult; auto.
End expo_congruence.
Fact Pell_sym x y : Pell x y <-> Pell y x.
Proof.
unfold Pell; split; intros H; rewrite <- H; ring.
End Pell.
Section divisibility_1.
Variable (b : nat) (Hb : 2 <= b) (k : nat) (Hk : k <> 0).
Let Hak : alpha_nat b k <> 0.
Proof.
apply alpha_nat_gt_0; auto.
Section equation.
Variable (m n l : nat) (Hm : m = n+l*k).
Infix "⊗" := (Zp_mult Hak) (at level 40, left associativity).
Notation expo := (mscal (Zp_mult Hak) (Zp_one Hak)).
Hint Resolve Zle_0_nat : core.
Section in_Z.
Notation "〚 x 〛" := (Z2Zp Hak x).
Let Z2ZP_morph := Z2Zp_morphishm Hak.
Open Scope Z_scope.
Fact A_k_morph22 : morph22 (Z2Zp Hak) (A b k) = (〚alpha_Z b (2+k)〛,Zp_zero Hak,Zp_zero Hak,〚-alpha_Z b k〛).
Proof using Hm.
destruct k as [ | k' ]; try lia.
unfold A; apply M22_equal; auto; simpl plus; unfold alpha_Z.
+
rewrite Z2Zp_opp, Z2Zp_pos, Nat2Z.id, nat2Zp_p, Zp_opp_zero; auto.
+
rewrite Z2Zp_pos, Nat2Z.id, nat2Zp_p; auto.
End in_Z.
Section in_nat.
Notation "〚 x 〛" := (nat2Zp Hak x).
End in_nat.
End equation.
End divisibility_1.
Section divisibility_2.
Variable (b : nat) (Hb : 2 <= b) (k : nat) (Hk : k <> 0).
Let Hak : alpha_nat b k <> 0.
Proof.
apply alpha_nat_gt_0; auto.
Let ak2 := alpha_nat b k * alpha_nat b k.
Let Hak2 : ak2 <> 0.
Proof.
unfold ak2; intros H.
apply mult_is_O in H; destruct H as [ H | H ]; revert H; apply alpha_nat_gt_0; auto.
Section equation.
Variable (m l : nat) (Hm : m = l*k) (Hl : l <> 0).
Infix "⊕" := (Zp_plus Hak2) (at level 50, left associativity).
Infix "⊗" := (Zp_mult Hak2) (at level 40, left associativity).
Notation expoZp := (mscal (Zp_mult Hak2) (Zp_one Hak2)).
Hint Resolve Zle_0_nat : core.
Section in_Zp.
Notation "〚 x 〛" := (Z2Zp Hak2 x).
Let Z2Zp_morph := Z2Zp_morphishm Hak2.
Open Scope Z_scope.
Let Zmult_monoid : monoid_theory Zmult 1.
Proof.
exists; intros; ring.
Notation MZp := (M22 ak2).
Infix "⊞" := (PL22 (Zp_plus Hak2)) (at level 50, left associativity).
Infix "⊠" := (MU22 (Zp_plus Hak2) (Zp_mult Hak2)) (at level 40, left associativity).
Notation MZp_Z := (ZE_22 (Zp_zero Hak2)).
Notation MZp_I := (ID_22 (Zp_zero Hak2) (Zp_one Hak2)).
Notation MZp_expo := (mscal (fun u v => u⊠v) MZp_I).
Notation MZp_scal := (M22scal (Zp_mult Hak2)).
Fact A_m_morph22 : morph22 (Z2Zp Hak2) (A b m) = MZp_scal (expoZp l〚-1〛⊗ expoZp l〚alpha_Z b k〛) MZp_I ⊞ MZp_scal (expoZp (l-1)〚-1〛⊗ nat2Zp Hak2 l ⊗ 〚alpha_Z b (S k)〛⊗ expoZp (l-1)〚alpha_Z b k〛) (morph22 (Z2Zp Hak2) (B b)).
Proof using Hl Hm.
generalize (MA_expo_A_binomial Hb _ _ Hm); intros H.
apply f_equal with (f := morph22 (Z2Zp Hak2)) in H.
rewrite msum_morph with (m2 := fun u v => u⊞v) (u2 := MZp_Z) in H.
2: simpl; apply M22_equal; apply Z2Zp_zero.
2: intros (((?&?)&?)&?) (((?&?)&?)&?); apply M22_equal; apply Z2Zp_plus.
rewrite msum_first_two in H; try lia.
2: apply M22plus_monoid with (1 := Zp_is_ring Hak2).
2: {
intros i Hi.
rewrite M22scal_morph with (1 := Z2Zp_morph).
repeat rewrite Z2Zp_mult.
replace i with (2+(i-2))%nat at 3 by lia.
rewrite mscal_plus, Z2Zp_mult; auto.
rewrite mscal_S, mscal_1; auto.
unfold alpha_Z at 1 2.
rewrite <- Nat2Z.inj_mul.
fold ak2.
rewrite (@Z2Zp_pos _ Hak2 (Z.of_nat ak2)); auto.
rewrite Nat2Z.id, nat2Zp_p.
repeat rewrite Zp_mult_zero.
rewrite (Zp_mult_comm _ _ (Zp_zero _)).
repeat rewrite Zp_mult_zero.
apply M22scal_zero with (1 := Zp_is_ring Hak2).
}
rewrite H.
repeat rewrite M22scal_morph with (1 := Z2Zp_morph).
repeat rewrite Z2Zp_mult.
rewrite binomial_n1; try lia.
rewrite binomial_n0.
rewrite Nat.sub_0_r.
repeat rewrite mscal_0.
repeat rewrite Z2Zp_one.
f_equal.
+
f_equal; auto.
2: apply M22_equal; try rewrite Z2Zp_one; auto; rewrite Z2Zp_zero; auto.
rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
2: rewrite Z2Zp_one; auto.
2: apply Z2Zp_mult.
rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
2: rewrite Z2Zp_one; auto.
2: apply Z2Zp_mult.
repeat rewrite <- Zp_mult_assoc.
repeat rewrite Zp_mult_one; auto.
+
repeat (rewrite mscal_1; auto).
2: apply M22mult_monoid with (1 := Zring).
rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
2: rewrite Z2Zp_one; auto.
2: apply Z2Zp_mult.
rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
2: rewrite Z2Zp_one; auto.
2: apply Z2Zp_mult.
do 4 f_equal.
rewrite Z2Zp_pos, Nat2Z.id; auto.
End in_Zp.
Add Ring myring2 : (Zp_is_ring Hak2).
End equation.
End divisibility_2.
Section congruence_1.
Variable (b1 b2 : nat) (Hb1 : 2 <= b1) (Hb2 : 2 <= b2) (q : nat) (Hq : q <> 0) (Hb : nat2Zp Hq b1 = nat2Zp Hq b2).
Hint Resolve Zle_0_nat : core.
End congruence_1.
Section congruence_2.
Variable (b : nat) (Hb : b - 2 <> 0).
Notation "〚 x 〛" := (Z2Zp Hb x).
Hint Resolve Zle_0_nat : core.
Open Scope Z_scope.
End congruence_2.
Section diophantine_sufficiency.
Variables (a b c : nat) (u t r s v w x y : nat).
Definition alpha_conditions := 3 < b /\ u*u+t*t = 1+b*(u*t) /\ s*s+r*r = 1+b*(s*r) /\ r < s /\ u*u │ s /\ v+2*r = b*s /\ rem w v = rem b v /\ rem w u = rem 2 u /\ 2 < w /\ x*x+y*y = 1+w*(x*y) /\ 2*a < u /\ 2*a < v /\ rem a v = rem x v /\ 2*c < u /\ rem c u = rem x u.
End diophantine_sufficiency.
Section diophantine_necessity.
Variables (a b c : nat).
End diophantine_necessity.

Fact MZ_det_B : MZ_det B = 1.
Proof.
Admitted.

Lemma MZ_det_A n : MZ_det (A n) = 1.
Proof using Hb_nat.
rewrite <- MZ_expo_A.
rewrite Det22_expo with (Rminus := Z.sub); auto.
rewrite MZ_det_B.
Admitted.

Theorem alpha_Pell n : Pell (α (S n)) (α n).
Proof using Hb_nat.
unfold Pell.
generalize (MZ_det_A n).
unfold A; simpl; intros H.
rewrite <- H.
Admitted.

Fact A_iA n : A n ⊠ iA n = MZ_one.
Proof using Hb_nat.
generalize (alpha_Pell n); unfold Pell; intros H.
Admitted.

Fact iA_A n : iA n ⊠ A n = MZ_one.
Proof using Hb_nat.
generalize (alpha_Pell n); unfold Pell; intros H.
Admitted.

Fact A_minus u v : (v <= u)%nat -> A (u-v)%nat = A u ⊠ iA v.
Proof using Hb_nat.
intros H.
rewrite <- (MZ_expo_A u).
replace u with (u-v+v)%nat at 2 by lia.
rewrite mscal_plus; auto.
do 2 rewrite MZ_expo_A.
rewrite <- M22mult_assoc with (1 := Zring).
rewrite A_iA.
rewrite M22mult_one_r with (1 := Zring).
Admitted.

Let A_eq_3_12 n : exists u v, u*α (S n) + v*α n = 1.
Proof.
generalize (alpha_Pell n); unfold Pell; intros H.
exists (α (S n)-b*α n), (α n).
Admitted.

Lemma alpha_nat_coprime n : is_gcd (alpha_nat (S n)) (alpha_nat n) 1.
Proof using Hb_nat.
Admitted.

Corollary alpha_nat_odd n : (rem (alpha_nat (S n)) 2 = 1 \/ rem (alpha_nat n) 2 = 1)%nat.
Proof using Hb_nat.
destruct rem_2_is_0_or_1 with (x := alpha_nat (S n)) as [ H1 | ]; auto.
destruct rem_2_is_0_or_1 with (x := alpha_nat n) as [ H2 | ]; auto.
exfalso; generalize (alpha_nat_coprime n); intros (_ & _ & H3).
Admitted.

Theorem find_odd_alpha u : exists n, (u <= alpha_nat (S n) /\ rem (alpha_nat (S n)) 2 = 1)%nat.
Proof using Hb_nat.
Admitted.

Fact expoZ_power n x : expoZ n (Z.of_nat x) = Z.of_nat (power n x).
Proof.
symmetry; apply mscal_morph; auto.
Admitted.

Fact mscal_Zplus n : mscal Zplus 0 n 1 = Z.of_nat n.
Proof.
induction n as [ | n IHn ].
+
rewrite mscal_0; auto.
+
rewrite mscal_S, IHn.
Admitted.

Theorem MA_expo_A_binomial m k l : (m = l * k)%nat -> A m = ∑ (S l) (fun i => MZ_scal ( expoZ (l-i) (-1) * Z.of_nat (binomial l i) * expoZ i (α (S k)) * expoZ (l-i) (α k) ) (MZ_expo i B)).
Proof using Hb_nat.
intro; subst m.
rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A, A_is_sum; auto.
rewrite binomial_Newton with (zero := MZ_zero); auto.
2: apply M22plus_comm with (1 := Zring).
2: apply M22plus_cancel with (1 := Zring).
2: apply M22_mult_distr_l with (1 := Zring).
2: apply M22_mult_distr_r with (1 := Zring).
2: apply M22_equal; ring.
apply msum_ext; intros i Hi.
repeat rewrite expo22_scal with (1 := Zring).
rewrite mscal_of_unit; auto.
rewrite <- M22scal_MU22_l with (1 := Zring).
rewrite <- M22scal_MU22_r with (1 := Zring).
rewrite M22mult_one_l with (1 := Zring).
rewrite M22scal_mult with (1 := Zring).
rewrite mscal_M22scal with (1 := Zring).
rewrite M22scal_mult with (1 := Zring).
f_equal.
rewrite mscal_Zplus.
replace (- α k) with ((-1)*α k) by ring.
Admitted.

Fact alpha_SSm_m_neq_0 : v <> 0%nat.
Proof using Hb_nat Hv.
intros H; subst; simpl in Hv.
Admitted.

Let Am_iAm_mod :〘A m〙= ⊟〘iA m〙.
Proof.
apply M22_equal.
+
rewrite Z2Zp_opp, Zp_opp_inv.
apply Z2Zp_inj.
exists 1; rewrite Hv; ring.
+
rewrite Z2Zp_opp; auto.
+
rewrite Z2Zp_opp, Zp_opp_inv; auto.
+
rewrite <- Z2Zp_opp.
apply Z2Zp_inj.
Admitted.

Fact A2m_mod : 〘A (2*m)〙= ⊟〘MZ_one〙.
Proof.
rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A; auto.
rewrite mscal_S, mscal_1; auto.
rewrite MU22_morph with (1 := Z2Zp_morph).
rewrite Am_iAm_mod at 1.
do 2 rewrite <- MI22_morph with (1 := Z2Zp_morph).
rewrite <- MU22_morph with (1 := Z2Zp_morph).
f_equal.
rewrite M22_opp_mult_l with (1 := Zring); f_equal.
Admitted.

Fact A2lm_mod : 〘A (2*l*m)〙= 〘MZ_scal (mscal Zmult 1 l (-1)) MZ_one〙.
Proof.
replace (2*l*m)%nat with (l*(2*m))%nat by ring.
rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A; auto.
rewrite expo22_morph with (1 := Z2Zp_morph).
rewrite A2m_mod.
rewrite <- MI22_morph with (1 := Z2Zp_morph).
rewrite <- expo22_morph with (1 := Z2Zp_morph).
f_equal.
rewrite <- M22scal_MI22 with (1 := Zring).
change (-(1)) with (-1).
rewrite expo22_scal with (1 := Zring); f_equal.
Admitted.

Let expoZ_opp1 i : expoZ i (-1) = 1 \/ expoZ i (-1) = -1.
Proof.
induction i as [ | i IHi ].
+
rewrite mscal_0; auto.
+
Admitted.

Fact alpha_2lm_plus_j :〚α (S (2*l*m+j))〛=〚expoZ l (-1)*α (S j)〛.
Proof.
generalize (A_plus (2*l*m) j); intros H.
apply f_equal with (f := morph22 f) in H.
rewrite MU22_morph with (1 := Z2Zp_morph) in H.
rewrite A2lm_mod in H.
rewrite <- MU22_morph with (1 := Z2Zp_morph) in H.
apply M22_proj12 in H.
rewrite Z.mul_0_r, Z.mul_0_l, Z.mul_1_r, Z.add_0_l in H.
Admitted.

Let Hj' : (j <= 2*l*m)%nat.
Proof.
apply le_trans with (1*m)%nat; try lia.
Admitted.

Theorem find_odd_alpha' u : exists n, (u <= alpha_nat n /\ rem (alpha_nat n) 2 = 1)%nat.
Proof using Hb_nat.
destruct (find_odd_alpha u) as (n & ?); exists (S n); auto.
