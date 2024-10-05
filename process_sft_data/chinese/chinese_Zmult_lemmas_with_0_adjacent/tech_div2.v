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

Lemma tech_div2 : forall n0 n q : nat, S n0 = q * S n -> neg n0 = multZ (pos n) (negOZ q).
intros n0 n q; elim q.
simpl in |- *; intros; absurd (S n0 = 0).
discriminate.
exact H.
intros y H; unfold negOZ in |- *.
rewrite (tech_mult_pos_negZ n y); intros.
simpl in H0; rewrite (eq_add_S _ _ H0).
elim (mult_commut (S n) y); simpl in |- *; elim (plus_comm (n + y) (n * y)).
elim (plus_assoc n y (n * y)); reflexivity.
