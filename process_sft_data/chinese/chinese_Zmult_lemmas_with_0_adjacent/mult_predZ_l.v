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

Lemma mult_predZ_l : forall x y : Z, multZ (predZ x) y = addZ (multZ x y) (oppZ y).
Proof.
intros; elim x.
simpl in |- *; reflexivity.
intros; elim n.
simpl in |- *; symmetry in |- *.
elim (addZ_opposite y I); intros.
elim H0; intros; elim H2; intros; exact H3.
intros; unfold predZ in |- *; rewrite (tech_mult_posZ n0 y).
elim (addZ_associativity (multZ (pos n0) y) y (oppZ y)).
elim (addZ_opposite y I); intros.
elim H1; intros; elim H3; intros; rewrite H4.
rewrite (add_OZ (multZ (pos n0) y)); reflexivity.
intros; reflexivity.
