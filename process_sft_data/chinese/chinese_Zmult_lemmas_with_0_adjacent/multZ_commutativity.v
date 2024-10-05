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

Theorem multZ_commutativity : commutativity Z multZ.
unfold commutativity in |- *; intros; elim x.
rewrite (mult_OZ y); unfold multZ in |- *; reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; exact (mult_IZ y).
intros y0 H; rewrite (tech_mult_posZ y0 y); rewrite H.
elim (mult_succZ_r y (pos y0)); unfold succZ in |- *; reflexivity.
intros; elim n.
simpl in |- *; symmetry in |- *; exact (mult_mIZ y).
intros y0 H; rewrite (tech_mult_negZ y0 y); rewrite H.
elim (mult_predZ_r y (neg y0)); unfold predZ in |- *; reflexivity.
