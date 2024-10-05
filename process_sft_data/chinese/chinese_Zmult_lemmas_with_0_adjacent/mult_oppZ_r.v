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

Lemma mult_oppZ_r : forall x y : Z, multZ x (oppZ y) = oppZ (multZ x y).
intros; case x.
reflexivity.
simple induction n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos y0) y) y I I).
elim H; reflexivity.
intros; elim n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (neg y0) y) (oppZ y) I I).
elim H; reflexivity.
