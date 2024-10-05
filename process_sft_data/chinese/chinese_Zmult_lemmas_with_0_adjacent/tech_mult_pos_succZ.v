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

Lemma tech_mult_pos_succZ : forall n m : nat, posOZ (S n * S m) = multZ (pos n) (pos m).
intros; elim m.
elim multZ_neutral; intros; elim (H0 (pos n) I); intros.
replace (pos 0) with IZ; auto.
rewrite H1.
elim (mult_commut 1 (S n)).
rewrite (mult_neutr (S n)).
unfold posOZ in |- *; reflexivity.
intros y H; elim (multZ_commutativity (pos (S y)) (pos n)).
rewrite (tech_mult_posZ y (pos n)); elim (multZ_commutativity (pos n) (pos y)).
elim H; elim (mult_n_Sm (S n) (S y)); elim (plus_n_Sm (S n * S y) n).
elim (mult_n_Sm (S n) y); elim (plus_n_Sm (S n * y) n).
unfold posOZ in |- *; rewrite (tech_add_pos_posZ (S n * y + n) n).
reflexivity.
