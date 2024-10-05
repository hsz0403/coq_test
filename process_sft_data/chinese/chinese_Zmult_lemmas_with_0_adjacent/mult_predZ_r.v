Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export Nat_complements.
Require Export groups.
Require Export rings.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.
Fixpoint multpos (x2 : Z) (n : nat) {struct n} : Z := match n with | O => x2 | S n0 => addZ (multpos x2 n0) x2 end.
Fixpoint multneg (x2 : Z) (n : nat) {struct n} : Z := match n with | O => oppZ x2 | S n0 => addZ (multneg x2 n0) (oppZ x2) end.
Definition multZ (x1 x2 : Z) := match x1 with | OZ => OZ | pos n => multpos x2 n | neg n => multneg x2 n end.

Lemma mult_predZ_r : forall x y : Z, multZ x (predZ y) = addZ (multZ x y) (oppZ x).
intros; elim x.
reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; exact (add_mIZ_predZ y).
intros n0 H; unfold oppZ in |- *; do 2 rewrite (tech_mult_posZ n0).
rewrite (pred_addZ_r (multZ (pos n0) (predZ y)) y).
elim (pred_addZ_l (multZ (pos n0) (predZ y)) y).
elim (addZ_commutativity y (multZ (pos n0) y)).
elim (addZ_associativity y (multZ (pos n0) y) (neg (S n0))).
elim (addZ_commutativity (addZ (multZ (pos n0) y) (neg (S n0))) y).
rewrite H; elim (pred_addZ_r (multZ (pos n0) y) (oppZ (pos n0))).
reflexivity.
simple induction n.
simpl in |- *.
replace (pos 0) with IZ; auto.
rewrite (add_IZ_succZ (oppZ y)).
exact (opp_predZ y).
intros n0 H; do 2 rewrite (tech_mult_negZ n0).
rewrite H; rewrite (opp_predZ y).
elim (addZ_commutativity (oppZ (neg n0)) (multZ (neg n0) y)).
elim (addZ_associativity (oppZ (neg n0)) (multZ (neg n0) y) (succZ (oppZ y))).
elim (addZ_commutativity (addZ (multZ (neg n0) y) (succZ (oppZ y))) (oppZ (neg n0))).
rewrite (succ_addZ_r (multZ (neg n0) y) (oppZ y)).
rewrite (succ_addZ_l (addZ (multZ (neg n0) y) (oppZ y)) (oppZ (neg n0))).
elim (succ_addZ_r (addZ (multZ (neg n0) y) (oppZ y)) (oppZ (neg n0))).
reflexivity.
