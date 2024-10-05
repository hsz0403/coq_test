Require Import NatAux.
Require Export NArith.
Require Import ZArith.
Open Scope N_scope.
Import BinPos.
Ltac to_nat_op := match goal with | H: (N.lt _ _) |- _ => generalize (Nlt_lt_rev _ _ H); clear H; intros H | H: (N.gt _ _) |- _ => generalize (Ngt_gt_rev _ _ H); clear H; intros H | H: (N.le _ _) |- _ => generalize (Nle_le_rev _ _ H); clear H; intros H | H: (N.ge _ _) |- _ => generalize (Nge_ge_rev _ _ H); clear H; intros H | H: (@eq N _ _) |- _ => generalize (Neq_eq_rev _ _ H); clear H; intros H | |- (N.lt _ _) => apply Nlt_lt | |- (N.le _ _) => apply Nle_le | |- (N.gt _ _) => apply Ngt_gt | |- (N.ge _ _) => apply Nge_ge | |- (@eq N _ _) => apply Nat2N.inj end.
Ltac set_to_nat := let nn := fresh "nn" in match goal with | |- context [(N.to_nat (?X + ?Y)%N)] => rewrite N2Nat.inj_add | |- context [(N.to_nat (?X * ?Y)%N)] => rewrite N2Nat.inj_mul | |- context [(N.to_nat ?X)] => set (nn:=N.to_nat X) in * |- * | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_add in H | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_mul in H | H: context [(N.to_nat ?X)] |- _ => set (nn:=N.to_nat X) in * |- * end.
Ltac to_nat := repeat to_nat_op; repeat set_to_nat.
Close Scope N_scope.

Theorem ge_Nge: forall n m, N.of_nat n >= N.of_nat m -> (n >= m)%nat.
Proof.
intros n m; case n; case m; unfold N.ge; simpl; try (intros; discriminate); auto with arith.
intros n1 H1; case H1; auto.
intros m1 n1 H1.
case (le_or_lt m1 n1); auto with arith.
intros H2; case H1.
apply nat_of_P_lt_Lt_compare_complement_morphism.
repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith.
