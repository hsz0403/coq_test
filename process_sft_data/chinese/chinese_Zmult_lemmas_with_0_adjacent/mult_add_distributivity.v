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

Theorem mult_add_distributivity : distributivity Z addZ multZ.
unfold distributivity in |- *; intros; case x.
split; reflexivity.
simple induction n.
split.
rewrite addZ_eq2; rewrite multZ_eq2.
rewrite (mult_succZ_l y z); exact (addZ_commutativity (multZ y z) z).
reflexivity.
intros y0 H.
elim H; intros; split.
rewrite addZ_eq3; rewrite multZ_eq3.
rewrite mult_succZ_l; rewrite H0.
elim (addZ_associativity (multZ (pos y0) z) (multZ y z) z).
elim (addZ_commutativity z (multZ y z)).
apply addZ_associativity.
do 3 rewrite multZ_eq3.
rewrite H1.
apply (add_add Z addZ addZ_commutativity addZ_associativity).
simple induction n.
split.
rewrite addZ_eq4; rewrite multZ_eq4; rewrite (mult_predZ_l y z).
exact (addZ_commutativity (multZ y z) (oppZ z)).
rewrite multZ_eq4.
apply (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity y z I I).
intros y0 H.
split.
rewrite (tech_add_neg_predZ y0 y); rewrite (mult_predZ_l (addZ (neg y0) y) z).
elim H; intros.
rewrite H0.
elim (addZ_associativity (multZ (neg y0) z) (multZ y z) (oppZ z)).
elim (addZ_commutativity (oppZ z) (multZ y z)).
rewrite (addZ_associativity (multZ (neg y0) z) (oppZ z) (multZ y z)).
elim (tech_mult_negZ y0 z); reflexivity.
rewrite (tech_mult_negZ y0 (addZ y z)); rewrite (tech_mult_negZ y0 y).
rewrite (tech_mult_negZ y0 z); elim H; intros; rewrite H1.
elim (add_add Z addZ addZ_commutativity addZ_associativity (multZ (neg y0) y) (multZ (neg y0) z) (oppZ y) (oppZ z)).
elim (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity y z I I).
reflexivity.
