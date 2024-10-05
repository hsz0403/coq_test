Require Import NatAux.
Require Export NArith.
Require Import ZArith.
Open Scope N_scope.
Import BinPos.
Ltac to_nat_op := match goal with | H: (N.lt _ _) |- _ => generalize (Nlt_lt_rev _ _ H); clear H; intros H | H: (N.gt _ _) |- _ => generalize (Ngt_gt_rev _ _ H); clear H; intros H | H: (N.le _ _) |- _ => generalize (Nle_le_rev _ _ H); clear H; intros H | H: (N.ge _ _) |- _ => generalize (Nge_ge_rev _ _ H); clear H; intros H | H: (@eq N _ _) |- _ => generalize (Neq_eq_rev _ _ H); clear H; intros H | |- (N.lt _ _) => apply Nlt_lt | |- (N.le _ _) => apply Nle_le | |- (N.gt _ _) => apply Ngt_gt | |- (N.ge _ _) => apply Nge_ge | |- (@eq N _ _) => apply Nat2N.inj end.
Ltac set_to_nat := let nn := fresh "nn" in match goal with | |- context [(N.to_nat (?X + ?Y)%N)] => rewrite N2Nat.inj_add | |- context [(N.to_nat (?X * ?Y)%N)] => rewrite N2Nat.inj_mul | |- context [(N.to_nat ?X)] => set (nn:=N.to_nat X) in * |- * | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_add in H | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_mul in H | H: context [(N.to_nat ?X)] |- _ => set (nn:=N.to_nat X) in * |- * end.
Ltac to_nat := repeat to_nat_op; repeat set_to_nat.
Close Scope N_scope.

Theorem Neq_eq_rev: forall n m, n = m -> (N.to_nat n = N.to_nat m)%nat.
Proof.
Admitted.

Theorem Nmult_lt_compat_l: forall n m p, n < m -> 0 < p -> p * n < p * m.
Proof.
intros n m p H1 H2; apply Nlt_lt; repeat rewrite N2Nat.inj_mul.
Admitted.

Theorem Nmult_le_compat_l: forall n m p, n <= m -> p * n <= p * m.
Proof.
intros n m p H1; apply Nle_le; repeat rewrite N2Nat.inj_mul.
Admitted.

Theorem Nmult_ge_compat_l: forall n m p, n >= m -> p * n >= p * m.
Proof.
intros n m p H1; apply Nge_ge; repeat rewrite N2Nat.inj_mul.
Admitted.

Theorem Nmult_gt_compat_l: forall n m p, n > m -> p > 0 -> p * n > p * m.
Proof.
intros n m p H1 H2; apply Ngt_gt; repeat rewrite N2Nat.inj_mul.
Admitted.

Theorem Nmult_lt_compat_rev_l1: forall n m p, p * n < p * m -> 0 < p.
Proof.
intros n m p H1; apply Nlt_lt; apply mult_lt_compat_rev_l1 with (nat_of_N n) (nat_of_N m).
Admitted.

Theorem Nmult_lt_compat_rev_l2: forall n m p, p * n < p * m -> n < m.
Proof.
intros n m p H1; apply Nlt_lt; apply mult_lt_compat_rev_l2 with (nat_of_N p).
Admitted.

Theorem Nmult_gt_compat_rev_l1: forall n m p, p * n > p * m -> p > 0.
Proof.
intros n m p H1; apply Ngt_gt; apply mult_gt_compat_rev_l1 with (nat_of_N n) (nat_of_N m).
Admitted.

Theorem Nmult_gt_compat_rev_l2: forall n m p, p * n > p * m -> n > m.
Proof.
intros n m p H1; apply Ngt_gt; apply mult_gt_compat_rev_l2 with (nat_of_N p).
Admitted.

Theorem Nmult_le_compat_rev_l: forall n m p, p * n <= p * m -> 0 < p -> n <= m.
Proof.
intros n m p H1 H2; apply Nle_le; apply mult_le_compat_rev_l with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply le_Nle; repeat rewrite N2Nat.id; auto.
Admitted.

Theorem Nlt_mult_0: forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
Admitted.

Theorem Ngt_mult_0: forall a b, a > 0 -> b > 0 -> a * b > 0.
Proof.
Admitted.

Theorem Nlt_mult_rev_0_l: forall a b, 0 < a * b -> 0 < a .
Proof.
intros a b H1; apply Nlt_lt; apply lt_mult_rev_0_l with (nat_of_N b).
Admitted.

Theorem Nlt_mult_rev_0_r: forall a b, 0 < a * b -> 0 < b .
Proof.
intros a b H1; apply Nlt_lt; apply lt_mult_rev_0_r with (nat_of_N a).
Admitted.

Theorem Ngt_mult_rev_0_l: forall a b, a * b > 0 -> a > 0.
Proof.
intros a b H1; apply Ngt_gt; apply gt_mult_rev_0_l with (nat_of_N b).
Admitted.

Theorem Ngt_mult_rev_0_r: forall a b, a * b > 0 -> b > 0 .
Proof.
intros a b H1; apply Ngt_gt; apply gt_mult_rev_0_r with (nat_of_N a).
Admitted.

Theorem Nle_0_eq_0: forall n, n <= 0 -> n = 0.
Proof.
intros n H1; rewrite <- (N2Nat.id n).
rewrite (le_0_eq_0 (nat_of_N n)); auto.
Admitted.

Theorem Nge_0_eq_0: forall n, 0 >= n -> n = 0.
Proof.
intros n H1; rewrite <- (N2Nat.id n).
rewrite (le_0_eq_0 (nat_of_N n)); auto.
change (0 >= nat_of_N n)%nat.
Admitted.

Theorem Nle_gt_trans: forall n m p, m <= n -> m > p -> n > p.
Proof.
Admitted.

Theorem Ngt_le_trans: forall n m p, n > m -> p <= m -> n > p.
Proof.
Admitted.

Theorem Nmult_ge_compat_rev_l: forall n m p , p * n >= p * m -> 0 < p -> n >= m.
Proof.
intros n m p H1 H2; apply Nge_ge; apply mult_ge_compat_rev_l with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply ge_Nge; repeat rewrite N2Nat.id; auto.
apply lt_Nlt; repeat rewrite N2Nat.id; auto.
