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

Lemma inversibleZ : forall x : Z, inversible Z multZ IZ x -> x = IZ \/ x = oppZ IZ.
simple destruct x.
intros; elim H; intros; elim H0; intros; elim H1.
left; reflexivity.
simple induction n.
intros; left; reflexivity.
intros y H H0; elim H0; intros; elim H1; intros.
absurd (multZ (pos (S y)) x0 = IZ).
elim x0.
rewrite (mult_OZ (pos (S y))).
discriminate.
intros; rewrite (tech_mult_pos_posZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *.
apply (tech_pos_not_posZ (S (y + (n0 + (n0 + y * n0)))) 0).
discriminate.
intros; rewrite (tech_mult_pos_negZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *; discriminate.
exact H2.
simple induction n.
right; reflexivity.
intros y H H0; elim H0; intros; elim H1; intros.
absurd (multZ (neg (S y)) x0 = IZ).
elim x0.
rewrite (mult_OZ (neg (S y))).
discriminate.
intros; rewrite (tech_mult_neg_posZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *; discriminate.
intros; rewrite (tech_mult_neg_negZ (S y) n0).
elim (plus_comm (S y + n0) (S y * n0)).
elim (plus_assoc (S y) n0 (S y * n0)); simpl in |- *.
apply (tech_pos_not_posZ (S (y + (n0 + (n0 + y * n0)))) 0).
discriminate.
exact H2.
