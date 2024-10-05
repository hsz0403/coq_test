Require Import NatAux.
Require Export NArith.
Require Import ZArith.
Open Scope N_scope.
Import BinPos.
Ltac to_nat_op := match goal with | H: (N.lt _ _) |- _ => generalize (Nlt_lt_rev _ _ H); clear H; intros H | H: (N.gt _ _) |- _ => generalize (Ngt_gt_rev _ _ H); clear H; intros H | H: (N.le _ _) |- _ => generalize (Nle_le_rev _ _ H); clear H; intros H | H: (N.ge _ _) |- _ => generalize (Nge_ge_rev _ _ H); clear H; intros H | H: (@eq N _ _) |- _ => generalize (Neq_eq_rev _ _ H); clear H; intros H | |- (N.lt _ _) => apply Nlt_lt | |- (N.le _ _) => apply Nle_le | |- (N.gt _ _) => apply Ngt_gt | |- (N.ge _ _) => apply Nge_ge | |- (@eq N _ _) => apply Nat2N.inj end.
Ltac set_to_nat := let nn := fresh "nn" in match goal with | |- context [(N.to_nat (?X + ?Y)%N)] => rewrite N2Nat.inj_add | |- context [(N.to_nat (?X * ?Y)%N)] => rewrite N2Nat.inj_mul | |- context [(N.to_nat ?X)] => set (nn:=N.to_nat X) in * |- * | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_add in H | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_mul in H | H: context [(N.to_nat ?X)] |- _ => set (nn:=N.to_nat X) in * |- * end.
Ltac to_nat := repeat to_nat_op; repeat set_to_nat.
Close Scope N_scope.

Theorem le_Nle: forall n m, N.of_nat n <= N.of_nat m -> (n <= m)%nat.
Proof.
intros n m; case n; case m; unfold N.le; simpl; auto with arith.
intros n1 H1; case H1; auto.
intros m1 n1 H1; case (le_or_lt n1 m1); auto with arith.
intros H2; case H1.
apply nat_of_P_gt_Gt_compare_complement_morphism.
Admitted.

Theorem Nle_le_rev: forall n m, n <= m -> (N.to_nat n <= N.to_nat m)%nat.
Proof.
Admitted.

Theorem Nlt_lt: forall n m, (N.to_nat n < N.to_nat m)%nat -> n < m.
Proof.
intros n m; case n; case m; unfold N.lt; simpl; try (intros; discriminate); auto.
intros H1; inversion H1.
intros p H1; inversion H1.
Admitted.

Theorem lt_Nlt: forall n m, N.of_nat n < N.of_nat m -> (n < m)%nat.
Proof.
intros n m; case n; case m; unfold N.lt; simpl; try (intros; discriminate); auto with arith.
intros m1 n1 H1.
rewrite <- (Nat2N.id (S n1)); rewrite <- (Nat2N.id (S m1)).
Admitted.

Theorem Nlt_lt_rev: forall n m, n < m -> (N.to_nat n < N.to_nat m)%nat.
Proof.
Admitted.

Theorem Nge_ge: forall n m, (N.to_nat n >= N.to_nat m)%nat -> n >= m.
Proof.
intros n m; case n; case m; unfold N.ge; simpl; try (intros; discriminate); auto.
intros p; elim p using Pind; simpl.
intros H1; inversion H1.
intros n1 _; rewrite nat_of_P_succ_morphism.
intros H1; inversion H1.
intros p1 p2 H1 H2; absurd (nat_of_P p2 < nat_of_P p1)%nat; auto with arith.
Admitted.

Theorem ge_Nge: forall n m, N.of_nat n >= N.of_nat m -> (n >= m)%nat.
Proof.
intros n m; case n; case m; unfold N.ge; simpl; try (intros; discriminate); auto with arith.
intros n1 H1; case H1; auto.
intros m1 n1 H1.
case (le_or_lt m1 n1); auto with arith.
intros H2; case H1.
apply nat_of_P_lt_Lt_compare_complement_morphism.
Admitted.

Theorem Nge_ge_rev: forall n m, n >= m -> (N.to_nat n >= N.to_nat m)%nat.
Proof.
Admitted.

Theorem Ngt_gt: forall n m, (N.to_nat n > N.to_nat m)%nat -> n > m.
Proof.
intros n m; case n; case m; unfold N.gt; simpl; try (intros; discriminate); auto.
intros H1; inversion H1.
intros p H1; inversion H1.
Admitted.

Theorem gt_Ngt: forall n m, N.of_nat n > N.of_nat m -> (n > m)%nat.
Proof.
intros n m; case n; case m; unfold N.gt; simpl; try (intros; discriminate); auto with arith.
intros m1 n1 H1.
rewrite <- (Nat2N.id (S n1)); rewrite <- (Nat2N.id (S m1)).
Admitted.

Theorem Ngt_gt_rev: forall n m, n > m -> (N.to_nat n > N.to_nat m)%nat.
Proof.
Admitted.

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

Theorem Nle_le: forall n m, (N.to_nat n <= N.to_nat m)%nat -> n <= m.
Proof.
intros n m; case n; case m; unfold N.le; simpl; try (intros; discriminate).
intros p; elim p using Pind; simpl.
intros H1; inversion H1.
intros n1 _; rewrite nat_of_P_succ_morphism.
intros H1; inversion H1.
intros p1 p2 H1 H2; absurd (nat_of_P p2 > nat_of_P p1)%nat; auto with arith.
apply nat_of_P_gt_Gt_compare_morphism; auto.
