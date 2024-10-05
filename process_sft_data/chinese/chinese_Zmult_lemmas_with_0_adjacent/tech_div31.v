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

Lemma tech_div31 : forall n q : nat, addZ (oppZ (multZ (pos n) (pos q))) (pos n) = oppZ (multZ (pos n) (posOZ q)).
intros; elim q.
unfold posOZ in |- *; rewrite (mult_OZ (pos n)).
cut (IZ = pos 0); intros.
elim H.
rewrite (mult_IZ (pos n)).
elim (addZ_opposite (pos n) I); intros; elim H1; intros; elim H3; intros.
rewrite H5; reflexivity.
reflexivity.
intros y H; unfold posOZ in |- *; elim (multZ_commutativity (pos (S y)) (pos n)).
rewrite (tech_mult_posZ y (pos n)).
rewrite (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos y) (pos n)) (pos n) I I).
elim (addZ_associativity (oppZ (multZ (pos y) (pos n))) (oppZ (pos n)) (pos n)).
elim (addZ_opposite (pos n) I); intros; elim H1; intros; elim H3; intros.
rewrite H5; rewrite (add_OZ (oppZ (multZ (pos y) (pos n)))).
elim (multZ_commutativity (pos y) (pos n)); reflexivity.
