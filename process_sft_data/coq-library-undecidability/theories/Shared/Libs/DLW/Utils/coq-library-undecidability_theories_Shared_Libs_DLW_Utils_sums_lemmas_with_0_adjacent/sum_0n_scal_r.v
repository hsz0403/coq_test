Require Import List Arith ZArith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list binomial.
Set Implicit Arguments.
Record monoid_theory (X : Type) (m : X -> X -> X) (u : X) := mk_monoid { monoid_unit_l : forall x, m u x = x; monoid_unit_r : forall x, m x u = x; monoid_assoc : forall x y z, m x (m y z) = m (m x y) z; }.
Fact Nat_plus_monoid : monoid_theory plus 0.
Proof.
exists; intros; ring.
Fact Nat_mult_monoid : monoid_theory mult 1.
Proof.
exists; intros; ring.
Fact Zplus_monoid : monoid_theory Zplus 0%Z.
Proof.
exists; intros; ring.
Fact Zmult_monoid : monoid_theory Zmult 1%Z.
Proof.
exists; intros; ring.
Hint Resolve Nat_plus_monoid Nat_mult_monoid Zplus_monoid Zmult_monoid : core.
Section msum.
Variable (X : Type) (m : X -> X -> X) (u : X).
Infix "⊕" := m (at level 50, left associativity).
Fixpoint msum n f := match n with | 0 => u | S n => f 0 ⊕ msum n (fun n => f (S n)) end.
Notation "∑" := msum.
Fact msum_fold_map n f : ∑ n f = fold_right m u (map f (list_an 0 n)).
Proof.
revert f; induction n as [ | n IHn ]; intros f; simpl; f_equal; auto.
rewrite IHn, <- map_S_list_an, map_map; auto.
Fact msum_0 f : ∑ 0 f = u.
Proof.
auto.
Fact msum_S n f : ∑ (S n) f = f 0 ⊕ ∑ n (fun n => f (S n)).
Proof.
auto.
Hypothesis Hmonoid : monoid_theory m u.
Fact msum_1 f : ∑ 1 f = f 0.
Proof.
destruct Hmonoid as [ H1 H2 ].
rewrite msum_S, msum_0, H2; auto.
Fact msum_plus a b f : ∑ (a+b) f = ∑ a f ⊕ ∑ b (fun i => f (a+i)).
Proof.
destruct Hmonoid as [ H1 _ H3 ].
revert f; induction a as [ | a IHa ]; intros f; simpl; auto.
rewrite <- H3; f_equal; apply IHa.
Fact msum_plus1 n f : ∑ (S n) f = ∑ n f ⊕ f n.
Proof.
destruct Hmonoid as [ _ H2 _ ].
replace (S n) with (n+1) by lia.
rewrite msum_plus; simpl; f_equal.
rewrite H2; f_equal; lia.
Fact msum_ext n f g : (forall i, i < n -> f i = g i) -> ∑ n f = ∑ n g.
Proof.
revert f g; induction n as [ | n IHn ]; intros f g Hfg; simpl; f_equal; auto.
+
apply Hfg; lia.
+
apply IHn; intros; apply Hfg; lia.
Fact msum_unit n : ∑ n (fun _ => u) = u.
Proof.
destruct Hmonoid as [ H1 _ _ ].
induction n as [ | n IHn ]; simpl; auto.
rewrite IHn; auto.
Fact msum_comm a n f : (forall i, i < n -> f i ⊕ a = a ⊕ f i) -> ∑ n f ⊕ a = a ⊕ ∑ n f.
Proof.
destruct Hmonoid as [ H1 H2 H3 ].
revert f; induction n as [ | n IHn ]; intros f H; simpl; auto.
+
rewrite H1, H2; auto.
+
rewrite H3, <- H; try lia.
repeat rewrite <- H3; f_equal.
apply IHn.
intros; apply H; lia.
Fact msum_sum n f g : (forall i j, i < j < n -> f j ⊕ g i = g i ⊕ f j) -> ∑ n (fun i => f i ⊕ g i) = ∑ n f ⊕ ∑ n g.
Proof.
destruct Hmonoid as [ H1 H2 H3 ].
revert f g; induction n as [ | n IHn ]; intros f g H; simpl; auto.
rewrite IHn.
+
repeat rewrite <- H3; f_equal.
repeat rewrite H3; f_equal.
symmetry; apply msum_comm.
intros; apply H; lia.
+
intros; apply H; lia.
Fact msum_of_unit n f : (forall i, i < n -> f i = u) -> ∑ n f = u.
Proof.
intros H.
rewrite <- (msum_unit n).
apply msum_ext; auto.
Fact msum_only_one n f i : i < n -> (forall j, j < n -> i <> j -> f j = u) -> ∑ n f = f i.
Proof.
destruct Hmonoid as [ M1 M2 M3 ].
intros H1 H2.
replace n with (i + 1 + (n-i-1)) by lia.
do 2 rewrite msum_plus.
rewrite msum_of_unit, msum_1, msum_of_unit, M1, M2.
+
f_equal; lia.
+
intros j Hj; destruct (H2 (i+1+j)); auto; lia.
+
intros j Hj; destruct (H2 j); auto; lia.
Fact msum_msum n k f : (forall i1 j1 i2 j2, i1 < n -> j1 < k -> i2 < n -> j2 < k -> f i1 j1 ⊕ f i2 j2 = f i2 j2 ⊕ f i1 j1) -> ∑ n (fun i => ∑ k (f i)) = ∑ k (fun j => ∑ n (fun i => f i j)).
Proof.
revert k f; induction n as [ | n IHn ]; intros k f Hf.
+
rewrite msum_0, msum_of_unit; auto.
+
rewrite msum_S, IHn.
*
rewrite <- msum_sum.
-
apply msum_ext.
intros; rewrite msum_S; trivial.
-
intros; symmetry; apply msum_comm.
intros; apply Hf; lia.
*
intros; apply Hf; lia.
Fact msum_ends n f : (forall i, 0 < i <= n -> f i = u) -> ∑ (n+2) f = f 0 ⊕ f (S n).
Proof.
destruct Hmonoid as [ H1 H2 H3 ].
intros H.
replace (n+2) with (1 + n + 1) by lia.
do 2 rewrite msum_plus; simpl.
rewrite msum_of_unit.
+
rewrite H2, H2, H2; do 2 f_equal; lia.
+
intros; apply H; lia.
Fact msum_first_two n f : 2 <= n -> (forall i, 2 <= i -> f i = u) -> ∑ n f = f 0 ⊕ f 1.
Proof.
destruct Hmonoid as [ _ M2 _ ].
intros Hn H1.
destruct n as [ | [ | n ] ]; try lia.
do 2 rewrite msum_S.
rewrite msum_of_unit.
+
rewrite M2; trivial.
+
intros; apply H1; lia.
Definition mscal n x := msum n (fun _ => x).
Fact mscal_0 x : mscal 0 x = u.
Proof.
apply msum_0.
Fact mscal_S n x : mscal (S n) x = x ⊕ mscal n x.
Proof.
apply msum_S.
Fact mscal_1 x : mscal 1 x = x.
Proof.
destruct Hmonoid as [ _ H2 _ ].
rewrite mscal_S, mscal_0, H2; trivial.
Fact mscal_of_unit n : mscal n u = u.
Proof.
apply msum_of_unit; auto.
Fact mscal_plus a b x : mscal (a+b) x = mscal a x ⊕ mscal b x.
Proof.
apply msum_plus.
Fact mscal_plus1 n x : mscal (S n) x = mscal n x ⊕ x.
Proof.
apply msum_plus1.
Fact mscal_comm n x y : x ⊕ y = y ⊕ x -> mscal n x ⊕ y = y ⊕ mscal n x.
Proof.
intros H; apply msum_comm; auto.
Fact mscal_sum n x y : x ⊕ y = y ⊕ x -> mscal n (x ⊕ y) = mscal n x ⊕ mscal n y.
Proof.
intro; apply msum_sum; auto.
Fact mscal_mult a b x : mscal (a*b) x = mscal a (mscal b x).
Proof.
induction a as [ | a IHa ]; simpl.
+
do 2 rewrite mscal_0; auto.
+
rewrite mscal_plus, IHa, mscal_S; auto.
Fact msum_mscal n k f : (forall i j, i < n -> j < n -> f i ⊕ f j = f j ⊕ f i) -> ∑ n (fun i => mscal k (f i)) = mscal k (∑ n f).
Proof.
intros H; apply msum_msum; auto.
End msum.
Section msum_morphism.
Variable (X Y : Type) (m1 : X -> X -> X) (u1 : X) (m2 : Y -> Y -> Y) (u2 : Y) (H1 : monoid_theory m1 u1) (H2 : monoid_theory m2 u2) (phi : X -> Y) (Hphi1 : phi u1 = u2) (Hphi2 : forall x y, phi (m1 x y) = m2 (phi x) (phi y)).
Fact msum_morph n f : phi (msum m1 u1 n f) = msum m2 u2 n (fun x => phi (f x)).
Proof.
revert f; induction n as [ | n IHn ]; intros f; simpl; auto.
rewrite Hphi2, IHn; trivial.
Fact mscal_morph n x : phi (mscal m1 u1 n x) = mscal m2 u2 n (phi x).
Proof.
apply msum_morph.
End msum_morphism.
Section binomial_Newton.
Variable (X : Type) (sum times : X -> X -> X) (zero one : X).
Infix "⊕" := sum (at level 50, left associativity).
Infix "⊗" := times (at level 40, left associativity).
Notation z := zero.
Notation o := one.
Notation scal := (mscal sum zero).
Notation expo := (mscal times one).
Hypothesis (M_sum : monoid_theory sum zero) (sum_comm : forall x y, x ⊕ y = y ⊕ x) (sum_cancel : forall x u v, x ⊕ u = x ⊕ v -> u = v) (M_times : monoid_theory times one) (distr_l : forall x y z, x ⊗ (y⊕z) = x⊗y ⊕ x⊗z) (distr_r : forall x y z, (y⊕z) ⊗ x = y⊗x ⊕ z⊗x).
Fact times_zero_l x : z ⊗ x = z.
Proof.
destruct M_sum as [ S1 S2 S3 ].
destruct M_times as [ T1 T2 T3 ].
apply sum_cancel with (z⊗x).
rewrite S2, <- distr_r, S1; trivial.
Fact times_zero_r x : x ⊗ z = z.
Proof.
destruct M_sum as [ S1 S2 S3 ].
destruct M_times as [ T1 T2 T3 ].
apply sum_cancel with (x⊗z).
rewrite S2, <- distr_l, S1; trivial.
Notation "∑" := (msum sum zero).
Fact sum_0n_scal n k f : ∑ n (fun i => scal k (f i)) = scal k (∑ n f).
Proof.
apply msum_mscal; auto.
Fact scal_times k x y : scal k (x⊗y) = x⊗scal k y.
Proof.
destruct M_sum as [ S1 S2 S3 ].
destruct M_times as [ T1 T2 T3 ].
induction k as [ | k IHk ].
+
rewrite mscal_0, mscal_0, times_zero_r; auto.
+
rewrite mscal_S, mscal_S, IHk, distr_l; auto.
Fact scal_one_comm k x : scal k o ⊗ x = x ⊗ scal k o.
Proof.
destruct M_times as [ T1 T2 T3 ].
induction k as [ | k IHk ].
+
rewrite mscal_0, times_zero_l, times_zero_r; auto.
+
rewrite mscal_S, distr_l, distr_r; f_equal; auto.
rewrite T1, T2; auto.
Fact sum_0n_distr_l b n f : ∑ n (fun i => b⊗f i) = b⊗∑ n f.
Proof.
revert f; induction n as [ | n IHn ]; intros f.
+
do 2 rewrite msum_0; rewrite times_zero_r; auto.
+
do 2 rewrite msum_S; rewrite IHn, distr_l; auto.
Fact sum_0n_distr_r b n f : ∑ n (fun i => f i⊗b) = ∑ n f ⊗ b.
Proof.
revert f; induction n as [ | n IHn ]; intros f.
+
do 2 rewrite msum_0; rewrite times_zero_l; auto.
+
do 2 rewrite msum_S; rewrite IHn, distr_r; auto.
End binomial_Newton.
Section Newton_nat.
Notation power := (mscal mult 1).
Notation "∑" := (msum plus 0).
Fact sum_fold_map n f : ∑ n f = fold_right plus 0 (map f (list_an 0 n)).
Proof.
apply msum_fold_map.
Fact power_0 x : power 0 x = 1.
Proof.
apply mscal_0.
Fact power_S n x : power (S n) x = x * power n x.
Proof.
apply mscal_S.
Fact power_1 x : power 1 x = x.
Proof.
apply mscal_1, Nat_mult_monoid.
Fact power_of_0 n : 0 < n -> power n 0 = 0.
Proof.
destruct n; try lia; rewrite power_S; auto.
Fact power_of_1 n : power n 1 = 1.
Proof.
rewrite mscal_of_unit; auto.
Fact power_plus p a b : power (a+b) p = power a p * power b p.
Proof.
apply mscal_plus, Nat_mult_monoid.
Fact power_mult p a b : power (a*b) p = power a (power b p).
Proof.
apply mscal_mult; auto.
Fact power_ge_1 k p : p <> 0 -> 1 <= power k p.
Proof.
intros Hp.
induction k as [ | k IHk ].
+
rewrite power_0; auto.
+
rewrite power_S.
apply (mult_le_compat 1 _ 1); lia.
Fact power2_gt_0 n : 0 < power n 2.
Proof.
apply power_ge_1; discriminate.
Fact power_sinc k p : 2 <= p -> power k p < power (S k) p.
Proof.
intros Hp; rewrite power_S.
rewrite <- (Nat.mul_1_l (power k p)) at 1.
apply mult_lt_compat_r; try lia.
apply power_ge_1; lia.
Fact power_ge_n k p : 2 <= p -> k <= power k p.
Proof.
intros Hp.
induction k as [ | k IHk ].
+
rewrite power_0; auto.
+
apply le_lt_trans with (2 := power_sinc _ Hp); auto.
Fact power_mono_l p q x : 1 <= x -> p <= q -> power p x <= power q x.
Proof.
intros Hx.
induction 1 as [ | q H IH ]; auto.
apply le_trans with (1 := IH).
rewrite power_S.
rewrite <- (Nat.mul_1_l (power _ _)) at 1.
apply mult_le_compat; auto.
Definition power_mono := power_mono_l.
Fact power_smono_l p q x : 2 <= x -> p < q -> power p x < power q x.
Proof.
intros H1 H2.
apply lt_le_trans with (1 := power_sinc _ H1).
apply power_mono_l; lia.
Fact power_mono_r n p q : p <= q -> power n p <= power n q.
Proof.
intros H.
induction n as [ | n IHn ].
+
do 2 rewrite power_0; auto.
+
do 2 rewrite power_S; apply mult_le_compat; auto.
Fact power_0_inv p n : power p n = 0 <-> n = 0 /\ 0 < p.
Proof.
induction p as [ | p IHp ].
+
rewrite power_0; lia.
+
rewrite power_S; split.
*
intros H.
apply mult_is_O in H.
rewrite IHp in H; lia.
*
intros (?&?); subst; simpl; auto.
Fact plus_cancel_l : forall a b c, a + b = a + c -> b = c.
Proof.
intros; lia.
Let plus_cancel_l':= plus_cancel_l.
Fact sum_0n_scal_l n k f : ∑ n (fun i => k*f i) = k*∑ n f.
Proof.
apply sum_0n_distr_l with (3 := Nat_mult_monoid); auto.
intros; ring.
Fact sum_0n_scal_r n k f : ∑ n (fun i => (f i)*k) = (∑ n f)*k.
Proof.
apply sum_0n_distr_r with (3 := Nat_mult_monoid); auto.
intros; ring.
Fact sum_0n_mono n f g : (forall i, i < n -> f i <= g i) -> ∑ n f <= ∑ n g.
Proof.
revert f g; induction n as [ | n IHn ]; intros f g H.
+
do 2 rewrite msum_0; auto.
+
do 2 rewrite msum_S; apply plus_le_compat.
*
apply H; lia.
*
apply IHn; intros; apply H; lia.
Fact sum_0n_le_one n f i : i < n -> f i <= ∑ n f.
Proof.
revert f i; induction n as [ | n IHn ]; intros f i H.
+
lia.
+
rewrite msum_S.
destruct i as [ | i ]; try lia.
apply lt_S_n, IHn with (f := fun i => f (S i)) in H.
lia.
Fact sum_power_lt k n f : k <> 0 -> (forall i, i < n -> f i < k) -> ∑ n (fun i => f i * power i k) < power n k.
Proof.
intros Hk.
revert f; induction n as [ | n IHn ]; intros f Hf.
+
rewrite msum_0, power_0; lia.
+
rewrite msum_S, power_S, power_0, Nat.mul_1_r.
apply le_trans with (k+ k * (power n k-1)).
*
apply (@plus_le_compat (S (f 0))).
-
apply Hf; lia.
-
rewrite msum_ext with (g := fun i => k*(f (S i)*power i k)).
++
rewrite sum_0n_distr_l with (one := 1); auto; try (intros; ring).
apply mult_le_compat_l.
apply le_S_n, le_trans with (power n k); try lia.
apply IHn; intros; apply Hf; lia.
++
intros; rewrite power_S; ring.
*
generalize (power_ge_1 n Hk); intros ?.
replace (power n k) with (1+(power n k - 1)) at 2 by lia.
rewrite Nat.mul_add_distr_l.
apply plus_le_compat; lia.
End Newton_nat.

Fact sum_0n_scal_r n k f : ∑ n (fun i => (f i)*k) = (∑ n f)*k.
Proof.
apply sum_0n_distr_r with (3 := Nat_mult_monoid); auto.
intros; ring.
