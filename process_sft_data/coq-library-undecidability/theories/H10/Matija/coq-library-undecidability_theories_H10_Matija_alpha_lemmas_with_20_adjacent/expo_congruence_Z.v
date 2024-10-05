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

Corollary alpha_nat_odd n : (rem (alpha_nat (S n)) 2 = 1 \/ rem (alpha_nat n) 2 = 1)%nat.
Proof using Hb_nat.
destruct rem_2_is_0_or_1 with (x := alpha_nat (S n)) as [ H1 | ]; auto.
destruct rem_2_is_0_or_1 with (x := alpha_nat n) as [ H2 | ]; auto.
exfalso; generalize (alpha_nat_coprime n); intros (_ & _ & H3).
Admitted.

Theorem find_odd_alpha u : exists n, (u <= alpha_nat (S n) /\ rem (alpha_nat (S n)) 2 = 1)%nat.
Proof using Hb_nat.
Admitted.

Theorem find_odd_alpha' u : exists n, (u <= alpha_nat n /\ rem (alpha_nat n) 2 = 1)%nat.
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
Admitted.

Theorem alpha_nat_2lm_plus_j : nat2Zp Hv' (alpha_nat (2*l*m+j)) = nat2Zp Hv' (alpha_nat j) \/ nat2Zp Hv' (alpha_nat (2*l*m+j)) = Zp_opp Hv' (nat2Zp Hv' (alpha_nat j)).
Proof.
generalize (alpha_2lm_plus_j).
destruct (expoZ_opp1 l) as [ E | E ]; rewrite E; intros H; [ left | right ].
+
repeat rewrite alpha_Z_S in H.
rewrite Z2Zp_of_nat, Z.mul_1_l, Z2Zp_of_nat in H; auto.
+
repeat rewrite alpha_Z_S in H.
change (-1) with (-(1)) in H.
rewrite Z.mul_opp_l, Z.mul_1_l, Z2Zp_opp in H.
Admitted.

Theorem alpha_nat_2lm_minus_j : nat2Zp Hv' (alpha_nat (2*l*m-j)) = nat2Zp Hv' (alpha_nat j) \/ nat2Zp Hv' (alpha_nat (2*l*m-j)) = Zp_opp Hv' (nat2Zp Hv' (alpha_nat j)).
Proof using Hl Hj.
generalize (alpha_2lm_minus_j).
destruct (expoZ_opp1 (S l)) as [ E | E ]; rewrite E; intros H; [ left | right ].
+
repeat rewrite alpha_Z_S in H.
rewrite Z2Zp_of_nat, Z.mul_1_l, Z2Zp_of_nat in H; auto.
+
repeat rewrite alpha_Z_S in H.
change (-1) with (-(1)) in H.
rewrite Z.mul_opp_l, Z.mul_1_l, Z2Zp_opp in H.
Admitted.

Let Hq : (1+q*q < b_nat*q)%nat.
Proof.
Admitted.

Let qz_eq :〚b〛⊗〚qz〛 ⊕ ∸ (〚qz〛⊗〚qz〛 ⊕〚1〛) = Zp_zero Hm.
Proof.
do 2 rewrite <- Z2Zp_mult.
rewrite <- Z2Zp_plus, <- Z2Zp_opp, <- Z2Zp_plus.
unfold b.
do 2 rewrite <- Nat2Z.inj_mul.
change 1 with (Z.of_nat 1%nat).
rewrite Z.add_opp_r, <- Nat2Z.inj_add, <- Nat2Z.inj_sub; try lia.
rewrite Nat.sub_add_distr; fold m.
Admitted.

Let BVP : 〘 B 〙 ⊠ 〘 VP 〙= scal〚qz〛〘 VP 〙.
Proof.
apply M22_equal; try rewrite Z2Zp_zero; try ring.
change (-1) with (-(1)).
rewrite Z2Zp_opp, Zp_opp_mult, <- (Z2Zp_mult _ 1).
rewrite Z.mul_1_l, <- (Zp_plus_zero Hm), <- qz_eq.
Admitted.

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
Admitted.

Theorem expo_congruence n : (0 < n)%nat -> nat2Zp Hm (q * alpha_nat n) = nat2Zp Hm (alpha_nat (n-1) + power n q).
Proof using Hb_nat.
destruct n as [ | n ]; try lia.
replace (S n-1)%nat with n by lia.
rewrite nat2Zp_mult.
generalize (expo_congruence_Z (S n)); intros H.
do 2 rewrite alpha_Z_S in H.
do 2 rewrite Z2Zp_of_nat in H.
Admitted.

Fact Pell_sym x y : Pell x y <-> Pell y x.
Proof.
Admitted.

Theorem Pell_zero_left y : Pell 0 y <-> y = 1 \/ y = -1.
Proof using Hb_nat.
unfold Pell; split.
+
intros H.
assert ((y-1)*(y+1) = 0) as H1.
{
ring_simplify in H.
ring_simplify; lia.
}
apply Zmult_integral in H1; lia.
+
Admitted.

Theorem Pell_zero_right x : Pell x 0 <-> x = 1 \/ x = -1.
Proof using Hb_nat.
Admitted.

Theorem Pell_not_diag x : ~ Pell x x.
Proof using Hb_nat.
unfold Pell.
intros H.
assert (x*((2-b)*x) = 1) as H1.
{
rewrite <- H; ring.
}
generalize H1; intros H2.
apply Z.eq_mul_1 in H1.
Admitted.

Theorem Pell_opposite_not x y : y < 0 -> 0 < x -> ~ Pell x y.
Proof using Hb_nat.
intros H1 H2 H3.
red in H3.
assert (0 <= - (b *x*y)) as H4.
{
replace (-(b*x*y)) with (b*x*-y) by ring.
apply Z.mul_nonneg_nonneg; try lia.
}
assert (0 < x*x) as H5.
{
apply Z.mul_pos_pos; auto.
}
assert (0 < y*y) as H6.
{
apply Z.mul_neg_neg; auto.
}
revert H3 H4 H5 H6.
Admitted.

Theorem Pell_alpha x y : 0 <= y < x -> Pell x y -> { n | x = α (S (S n)) /\ y = α (S n) }.
Proof using Hb_nat.
induction on x y as IH with measure (Z.to_nat y); intros Hxy HP.
destruct (Z.eq_dec y 0) as [ Hy | Hy ].
+
exists 0%nat.
rewrite alpha_fix_1, alpha_fix_2; split; auto.
subst y; rewrite Pell_zero_right in HP; lia.
+
red in HP.
assert (x*x = 1 + (b*y)*x - y*y) as H1.
{
rewrite <- HP; ring.
}
assert (0 < y*y) as H2.
{
apply Z.mul_pos_pos; lia.
}
assert (x <= (b*y)) as H3.
{
apply Zmult_le_reg_r with x; [ | rewrite H1 ]; lia.
}
assert (-(y*x) <= - (y*y)) as H4.
{
rewrite <- Z.opp_le_mono.
apply Zmult_le_compat; lia.
}
assert (x > b*y-y) as H5.
{
apply Zmult_gt_reg_r with x; try lia.
}
destruct (IH y (b*y-x)) as (m & G1 & G2); try lia.
-
red; rewrite <- HP; ring.
-
exists (S m); split; auto.
Admitted.

Theorem alpha_nat_Pell b n : 2 <= b -> alpha_nat b (S n)*alpha_nat b (S n) + alpha_nat b n * alpha_nat b n = 1 + b*(alpha_nat b (S n) * alpha_nat b n).
Proof.
intros Hb.
generalize (alpha_Pell Hb (S n)); intros H; red in H.
unfold alpha_Z in H.
apply Nat2Z.inj.
repeat rewrite Nat2Z.inj_add.
repeat rewrite Nat2Z.inj_mul.
change (Z.of_nat 1) with (1%Z).
Admitted.

Theorem alpha_nat_Pell' b n : 2 <= b -> alpha_nat b n*alpha_nat b n + alpha_nat b (S n) * alpha_nat b (S n) = 1 + b*(alpha_nat b n * alpha_nat b (S n)).
Proof.
rewrite plus_comm, (mult_comm (alpha_nat b n) (alpha_nat b (S n))).
Admitted.

Theorem Pell_alpha_nat b x y : 2 <= b -> y <= x -> x*x+y*y = 1+b*(x*y) -> { n | x = alpha_nat b (S n) /\ y = alpha_nat b n }.
Proof.
intros Hb H2 H1.
apply f_equal with (f := Z.of_nat) in H1.
do 2 rewrite Nat2Z.inj_add in H1.
do 4 rewrite Nat2Z.inj_mul in H1.
simpl Z.of_nat in H1.
apply Z.sub_move_r in H1.
destruct (le_lt_dec x y) as [ H3 | H3 ].
+
revert H1; replace y with x by lia; clear y H2 H3; intros H1.
exfalso.
apply (@Pell_not_diag _ Hb (Z.of_nat x)); red.
rewrite <- H1; ring.
+
destruct (@Pell_alpha _ Hb (Z.of_nat x) (Z.of_nat y)) as (n & P1 & P2).
*
split.
-
apply Zle_0_nat.
-
apply inj_lt; trivial.
*
red; rewrite <- H1; ring.
*
unfold alpha_Z in P1, P2.
apply Nat2Z.inj in P1.
apply Nat2Z.inj in P2.
Admitted.

Corollary Pell_alpha_nat' b x y : 2 <= b -> x*x+y*y = 1+b*(x*y) -> { n | x = alpha_nat b n }.
Proof.
intros H1 H2.
destruct (le_lt_dec y x) as [ H3 | H3 ].
+
destruct Pell_alpha_nat with (3 := H2) as (n & ? & ?); auto.
exists (S n); auto.
+
rewrite plus_comm, (mult_comm x y) in H2.
destruct Pell_alpha_nat with (3 := H2) as (n & ? & ?); auto; try lia.
Admitted.

Theorem alpha_nat_2lm b n m l j v : 2 <= b -> v = alpha_nat b (S (S m)) - alpha_nat b m -> arem n (S m) l j -> rem (alpha_nat b n) v = rem (alpha_nat b j) v \/ rem (alpha_nat b n + alpha_nat b j) v = 0.
Proof.
intros Hb Hv.
assert (Hv' : Z.of_nat v = (alpha_Z b (S(2 + m)) - alpha_Z b (S m))%Z).
{
rewrite Hv.
rewrite Nat2Z.inj_sub; auto.
apply lt_le_weak, alpha_nat_smono; lia.
}
intros (Hk & [ Hl | (Hl1 & Hl2) ] ).
+
destruct alpha_nat_2lm_plus_j with (Hb_nat := Hb) (Hv := Hv') (l := l) (j := j) as [ H | H ].
-
rewrite nat2Zp_inj in H; subst; auto.
-
right; rewrite <- rem_of_0 with v.
rewrite <- nat2Zp_inj with (Hp := alpha_SSm_m_neq_0 Hb (S m) Hv').
rewrite nat2Zp_plus, Hl, H, Zp_plus_comm, Zp_minus, nat2Zp_zero; auto.
+
destruct alpha_nat_2lm_minus_j with (Hb_nat := Hb) (Hv := Hv') (l := l) (j := j) as [ H | H ]; auto.
-
rewrite nat2Zp_inj in H; subst; auto.
-
right; rewrite <- rem_of_0 with v.
rewrite <- nat2Zp_inj with (Hp := alpha_SSm_m_neq_0 Hb (S m) Hv').
Admitted.

Let Hak : alpha_nat b k <> 0.
Proof.
Admitted.

Fact A_k_morph22 : morph22 (Z2Zp Hak) (A b k) = (〚alpha_Z b (2+k)〛,Zp_zero Hak,Zp_zero Hak,〚-alpha_Z b k〛).
Proof using Hm.
destruct k as [ | k' ]; try lia.
unfold A; apply M22_equal; auto; simpl plus; unfold alpha_Z.
+
rewrite Z2Zp_opp, Z2Zp_pos, Nat2Z.id, nat2Zp_p, Zp_opp_zero; auto.
+
Admitted.

Lemma alpha_Z_mnlk_eq : 〚 alpha_Z b (1+m) 〛 = 〚 alpha_Z b (1+n) 〛⊗ expo l〚 alpha_Z b (2+k) 〛.
Proof using Hm.
generalize (A_plus_mult Hb _ _ _ Hm); intros H.
apply f_equal with (f := morph22 (Z2Zp Hak)) in H.
rewrite MU22_morph with (1 := Z2ZP_morph) in H.
rewrite expo22_morph with (1 := Z2ZP_morph) in H.
rewrite A_k_morph22 in H.
rewrite Diag22_expo with (1 := Zp_is_ring Hak) in H.
unfold A, morph22 in H.
rewrite MU22_Diag22 with (1 := Zp_is_ring Hak) in H.
Admitted.

Theorem alpha_nat_mnlk_eq : 〚 alpha_nat b m 〛 = 〚 alpha_nat b n 〛⊗ expo l〚 alpha_nat b (1+k) 〛.
Proof using Hm.
generalize alpha_Z_mnlk_eq.
simpl plus.
unfold alpha_Z.
do 3 (rewrite Z2Zp_pos; auto).
Admitted.

Theorem alpha_nat_divides_k_ge_1 m : alpha_nat b k │ alpha_nat b m <-> k │ m.
Proof using Hak.
split.
+
intros H1.
destruct (euclid m Hk) as (l & [ | n ] & E1 & E2).
{
exists l; lia.
}
rewrite plus_comm in E1.
generalize (alpha_nat_mnlk_eq _ _ E1); intros H2.
rewrite <- nat2Zp_expo, <- nat2Zp_mult in H2.
apply nat2Zp_divides in H2; auto.
apply is_rel_prime_div_r in H2.
2: apply is_rel_prime_expo, is_gcd_sym, alpha_nat_coprime; auto.
apply divides_le in H2.
*
apply alpha_nat_smono with (1 := Hb) in E2; lia.
*
apply alpha_nat_gt_0; lia.
+
intros (l & Hl).
generalize (alpha_nat_mnlk_eq 0 _ Hl); intros H2.
rewrite <- nat2Zp_expo, <- nat2Zp_mult in H2.
simpl in H2.
rewrite nat2Zp_inj in H2.
rewrite rem_of_0 in H2.
generalize (div_rem_spec1 (alpha_nat b m) (alpha_nat b k)).
Admitted.

Theorem alpha_nat_divisibility_1 b k m : 2 <= b -> alpha_nat b k │ alpha_nat b m <-> k │ m.
Proof.
intros Hb.
destruct (eq_nat_dec k 0) as [ | Hk ]; subst.
+
simpl; split; intros H; apply divides_0_inv in H.
-
destruct (eq_nat_dec m 0) as [ | Hm ]; subst.
*
apply divides_0.
*
generalize (alpha_nat_gt_0 Hb Hm); lia.
-
subst; apply divides_0.
+
Admitted.

Let Hak : alpha_nat b k <> 0.
Proof.
Admitted.

Let Hak2 : ak2 <> 0.
Proof.
unfold ak2; intros H.
Admitted.

Theorem expo_congruence_Z n : nat2Zp Hm q ⊗〚α (S n)〛=〚α n〛⊕ nat2Zp Hm (power n q).
Proof using Hb_nat.
destruct Z2Zp_morph as [ G1 G2 G3 G4 G5 ].
generalize (AnVP n); intros H.
apply M22_proj12 in H.
rewrite Z2Zp_one in H.
do 2 rewrite Zp_mult_one_r in H.
rewrite expoZ_power in H.
rewrite (Z2Zp_of_nat _ (power _ _)) in H.
rewrite <- H, Z2Zp_of_nat.
simpl plus; rewrite Z2Zp_opp; ring.
