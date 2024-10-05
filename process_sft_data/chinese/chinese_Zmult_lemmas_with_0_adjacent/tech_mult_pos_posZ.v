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

Lemma tech_mult_pos_posZ : forall n m : nat, multZ (pos n) (pos m) = pos (n * m + (n + m)).
intros; elim n.
reflexivity.
intros y H; rewrite (tech_mult_posZ y (pos m)); rewrite H.
rewrite (tech_add_pos_posZ (y * m + (y + m)) m).
elim (technical_lemma y m); reflexivity.
