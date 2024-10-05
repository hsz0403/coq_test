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

Lemma mult_succZ_r : forall x y : Z, multZ x (succZ y) = addZ (multZ x y) x.
intros; elim x.
reflexivity.
simple induction n.
symmetry in |- *; exact (add_IZ_succZ y).
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; elim (addZ_commutativity (pos y0) (multZ (pos y0) y)).
elim (addZ_associativity (pos y0) (multZ (pos y0) y) (succZ y)).
elim (addZ_commutativity (addZ (multZ (pos y0) y) (succZ y)) (pos y0)).
rewrite (succ_addZ_r (multZ (pos y0) y) y).
rewrite (succ_addZ_l (addZ (multZ (pos y0) y) y) (pos y0)).
elim (succ_addZ_r (addZ (multZ (pos y0) y) y) (pos y0)).
reflexivity.
simple induction n.
simpl in |- *; rewrite (add_mIZ_predZ (oppZ y)); exact (opp_succZ y).
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
elim H; elim (addZ_commutativity (oppZ y) (multZ (neg y0) y)).
elim (addZ_associativity (oppZ y) (multZ (neg y0) y) (neg (S y0))).
elim (addZ_commutativity (addZ (multZ (neg y0) y) (neg (S y0))) (oppZ y)).
rewrite (opp_succZ y).
rewrite (pred_addZ_r (multZ (neg y0) (succZ y)) (oppZ y)).
rewrite H; elim (pred_addZ_l (addZ (multZ (neg y0) y) (neg y0)) (oppZ y)).
elim (pred_addZ_r (multZ (neg y0) y) (neg y0)); unfold predZ in |- *; reflexivity.
