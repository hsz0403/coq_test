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

Lemma mult_mIZ : forall x : Z, multZ x (neg 0) = oppZ x.
simple destruct x.
reflexivity.
simple induction n.
reflexivity.
intros y H; rewrite (tech_mult_posZ y (neg 0)); rewrite H.
rewrite (add_mIZ_predZ (oppZ (pos y))); reflexivity.
simple induction n.
reflexivity.
intros y H; rewrite (tech_mult_negZ y (neg 0)); rewrite H.
elim (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (neg y) (neg 0) I I).
rewrite (add_mIZ_predZ (neg y)); reflexivity.
