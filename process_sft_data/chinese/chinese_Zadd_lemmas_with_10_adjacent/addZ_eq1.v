Require Export Arith.
Require Export Nat_complements.
Require Export Lci.
Require Export groups.
Require Export rings.
Require Export Zbase.
Require Export Z_succ_pred.
Fixpoint addpos (x2 : Z) (n : nat) {struct n} : Z := match n with | O => succZ x2 | S n0 => succZ (addpos x2 n0) end.
Fixpoint addneg (x2 : Z) (n : nat) {struct n} : Z := match n with | O => predZ x2 | S n0 => predZ (addneg x2 n0) end.
Definition addZ (x1 x2 : Z) := match x1 with | OZ => x2 | pos n => addpos x2 n | neg n => addneg x2 n end.
Definition IdZ (x : Z) := True.
Definition oppZ (x : Z) := match x return Z with | OZ => (* OZ *) OZ (* pos n *) | pos n => neg n (* neg n *) | neg n => pos n end.

Lemma addZ_eq2 : forall y : Z, addZ (pos 0) y = succZ y.
Proof.
Admitted.

Lemma addZ_eq3 : forall (n1 : nat) (y : Z), addZ (pos (S n1)) y = succZ (addZ (pos n1) y).
Proof.
Admitted.

Lemma addZ_eq4 : forall y : Z, addZ (neg 0) y = predZ y.
Proof.
Admitted.

Lemma addZ_eq5 : forall (n1 : nat) (y : Z), addZ (neg (S n1)) y = predZ (addZ (neg n1) y).
Proof.
Admitted.

Lemma succ_addZ_l : forall x y : Z, addZ (succZ x) y = succZ (addZ x y).
intros; elim x.
reflexivity.
trivial.
simple destruct n.
simpl in |- *; symmetry in |- *; exact (succ_predZ y).
intros; symmetry in |- *; rewrite addZ_eq5.
Admitted.

Lemma pred_addZ_l : forall x y : Z, addZ (predZ x) y = predZ (addZ x y).
intros; elim x.
reflexivity.
simple destruct n.
simpl in |- *; rewrite pred_succZ; trivial.
intros; rewrite addZ_eq3; rewrite pred_succZ; trivial.
Admitted.

Lemma succ_addZ_r : forall x y : Z, addZ x (succZ y) = succZ (addZ x y).
intros; elim x.
reflexivity.
simple induction n.
reflexivity.
intros.
do 2 rewrite (tech_add_pos_succZ n0).
elim H; reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; apply succ_pred_pred_succZ.
intros.
do 2 rewrite (tech_add_neg_predZ n0).
rewrite H.
Admitted.

Lemma pred_addZ_r : forall x y : Z, addZ x (predZ y) = predZ (addZ x y).
intros; elim x.
reflexivity.
simple induction n.
simpl in |- *; apply succ_pred_pred_succZ.
intros.
do 2 rewrite (tech_add_pos_succZ n0).
rewrite H; apply succ_pred_pred_succZ.
simple induction n.
reflexivity.
intros.
do 2 rewrite (tech_add_neg_predZ n0).
Admitted.

Lemma add_OZ : forall x : Z, addZ x OZ = x.
simple induction x.
reflexivity.
simple induction n.
reflexivity.
intros; rewrite tech_add_pos_succZ; rewrite H; reflexivity.
simple induction n.
reflexivity.
Admitted.

Lemma add_IZ_succZ : forall x : Z, addZ x IZ = succZ x.
intros.
cut (succZ OZ = IZ); intros.
elim H.
rewrite (succ_addZ_r x OZ); rewrite (add_OZ x); reflexivity.
Admitted.

Lemma addZ_eq1 : forall y : Z, addZ OZ y = y.
Proof.
auto with arith.
