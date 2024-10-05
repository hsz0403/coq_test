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

Lemma tech_div3 : forall n0 n q r : nat, S n0 = q * S n + r -> S n > r -> neg n0 = addZ (multZ (pos n) (neg q)) (pos (n - r)).
intros.
elim (tech_opp_pos_negZ q); intros; elim H1.
rewrite (mult_oppZ_r (pos n) (pos q)); rewrite (tech_div32 n q r H0).
rewrite (addZ_associativity (oppZ (multZ (pos n) (pos q))) (pos n) (oppZ (posOZ r))) .
rewrite (tech_div31 n q).
elim (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos n) (posOZ q)) (posOZ r) I I).
elim (tech_div1 n0 n q r H); reflexivity.
