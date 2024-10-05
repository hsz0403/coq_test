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

Lemma tech_div1 : forall n0 n q r : nat, S n0 = q * S n + r -> pos n0 = addZ (multZ (pos n) (posOZ q)) (posOZ r).
intros n0 n q r; elim q.
elim r.
intros; absurd (S n0 = 0).
discriminate.
exact H.
intros y H; unfold posOZ in |- *; rewrite (mult_OZ (pos n)).
simpl in |- *; intros; elim (eq_add_S n0 y H0); reflexivity.
elim r.
intros y H; unfold posOZ in |- *; elim (plus_n_O (S y * S n)).
rewrite (add_OZ (multZ (pos n) (pos y))); elim (tech_mult_pos_succZ n y).
elim (mult_commut (S n) (S y)); intros; elim H0; unfold posOZ in |- *; reflexivity.
intros y H y0 H0; unfold posOZ in |- *; elim (plus_n_Sm (S y0 * S n) y).
intros; rewrite (eq_add_S n0 (S y0 * S n + y) H1).
rewrite (tech_mult_pos_succZ2 n y0).
rewrite (tech_add_pos_posZ (S n * y0 + n) y).
elim (plus_comm n (S n * y0)); elim (mult_commut y0 (S n)); simpl in |- *.
reflexivity.
