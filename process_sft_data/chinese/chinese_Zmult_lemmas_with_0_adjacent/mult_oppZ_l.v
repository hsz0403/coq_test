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

Lemma mult_oppZ_l : forall x y : Z, multZ (oppZ x) y = oppZ (multZ x y).
simple destruct y.
rewrite (mult_OZ (oppZ x)); rewrite (mult_OZ x); reflexivity.
intros; elim (multZ_commutativity (pos n) (oppZ x)).
elim (multZ_commutativity (pos n) x); elim n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; symmetry in |- *.
exact (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos y0) x) x I I).
intros; elim (multZ_commutativity (neg n) (oppZ x)).
elim (multZ_commutativity (neg n) x); elim n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite H; symmetry in |- *.
exact (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (neg y0) x) (oppZ x) I I).
