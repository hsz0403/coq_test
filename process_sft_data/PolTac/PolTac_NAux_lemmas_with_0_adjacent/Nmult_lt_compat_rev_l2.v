Require Import NatAux.
Require Export NArith.
Require Import ZArith.
Open Scope N_scope.
Import BinPos.
Ltac to_nat_op := match goal with | H: (N.lt _ _) |- _ => generalize (Nlt_lt_rev _ _ H); clear H; intros H | H: (N.gt _ _) |- _ => generalize (Ngt_gt_rev _ _ H); clear H; intros H | H: (N.le _ _) |- _ => generalize (Nle_le_rev _ _ H); clear H; intros H | H: (N.ge _ _) |- _ => generalize (Nge_ge_rev _ _ H); clear H; intros H | H: (@eq N _ _) |- _ => generalize (Neq_eq_rev _ _ H); clear H; intros H | |- (N.lt _ _) => apply Nlt_lt | |- (N.le _ _) => apply Nle_le | |- (N.gt _ _) => apply Ngt_gt | |- (N.ge _ _) => apply Nge_ge | |- (@eq N _ _) => apply Nat2N.inj end.
Ltac set_to_nat := let nn := fresh "nn" in match goal with | |- context [(N.to_nat (?X + ?Y)%N)] => rewrite N2Nat.inj_add | |- context [(N.to_nat (?X * ?Y)%N)] => rewrite N2Nat.inj_mul | |- context [(N.to_nat ?X)] => set (nn:=N.to_nat X) in * |- * | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_add in H | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_mul in H | H: context [(N.to_nat ?X)] |- _ => set (nn:=N.to_nat X) in * |- * end.
Ltac to_nat := repeat to_nat_op; repeat set_to_nat.
Close Scope N_scope.

Theorem Nmult_lt_compat_rev_l2: forall n m p, p * n < p * m -> n < m.
Proof.
intros n m p H1; apply Nlt_lt; apply mult_lt_compat_rev_l2 with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
