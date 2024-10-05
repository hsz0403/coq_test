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

Lemma tech_div4 : forall n0 n q r : nat, S n0 = q * S n + r -> pos n0 = addZ (multZ (neg n) (negOZ q)) (posOZ r).
intros; cut (multZ (neg n) (negOZ q) = multZ (pos n) (posOZ q)); intros.
rewrite H0; intros; exact (tech_div1 n0 n q r H).
cut (negOZ q = oppZ (posOZ q)); intros.
rewrite H0.
elim (tech_opp_pos_negZ n); intros; elim H1.
apply (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring (pos n) (posOZ q) I I).
elim q; reflexivity.
