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

Lemma multZ_eq1 : forall n : Z, multZ OZ n = OZ.
Proof.
Admitted.

Lemma multZ_eq2 : forall n : Z, multZ (pos 0) n = n.
Proof.
Admitted.

Lemma multZ_eq4 : forall n : Z, multZ (neg 0) n = oppZ n.
Proof.
Admitted.

Lemma multZ_eq5 : forall (n1 : nat) (n : Z), multZ (neg (S n1)) n = addZ (multZ (neg n1) n) (oppZ n).
Proof.
Admitted.

Lemma mult_succZ_l : forall x y : Z, multZ (succZ x) y = addZ (multZ x y) y.
intros; elim x.
simpl in |- *; reflexivity.
intros; simpl in |- *; reflexivity.
intros; elim n.
simpl in |- *; symmetry in |- *.
elim (addZ_opposite y I); intros.
elim H0; intros; elim H2; intros; exact H4.
intros; unfold succZ in |- *; rewrite (tech_mult_negZ n0 y).
elim (addZ_associativity (multZ (neg n0) y) (oppZ y) y).
elim (addZ_opposite y I); intros.
elim H1; intros; elim H3; intros.
rewrite H5.
Admitted.

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
Admitted.

Lemma mult_succZ_r : forall x y : Z, multZ x (succZ y) = addZ (multZ x y) x.
intros; elim x.
reflexivity.
simple induction n.
symmetry in |- *; exact (add_IZ_succZ y).
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; elim (addZ_commutativity (pos y0) (multZ (pos y0) y)).
elim (addZ_associativity (pos y0) (multZ (pos y0) y) (succZ y)).
elim (addZ_commutativity (addZ (multZ (pos y0) y) (succZ y)) (pos y0)).
rewrite (succ_addZ_r (multZ (pos y0) y) y).
rewrite (succ_addZ_l (addZ (multZ (pos y0) y) y) (pos y0)).
elim (succ_addZ_r (addZ (multZ (pos y0) y) y) (pos y0)).
reflexivity.
simple induction n.
simpl in |- *; rewrite (add_mIZ_predZ (oppZ y)); exact (opp_succZ y).
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
elim H; elim (addZ_commutativity (oppZ y) (multZ (neg y0) y)).
elim (addZ_associativity (oppZ y) (multZ (neg y0) y) (neg (S y0))).
elim (addZ_commutativity (addZ (multZ (neg y0) y) (neg (S y0))) (oppZ y)).
rewrite (opp_succZ y).
rewrite (pred_addZ_r (multZ (neg y0) (succZ y)) (oppZ y)).
rewrite H; elim (pred_addZ_l (addZ (multZ (neg y0) y) (neg y0)) (oppZ y)).
Admitted.

Lemma mult_predZ_r : forall x y : Z, multZ x (predZ y) = addZ (multZ x y) (oppZ x).
intros; elim x.
reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; exact (add_mIZ_predZ y).
intros n0 H; unfold oppZ in |- *; do 2 rewrite (tech_mult_posZ n0).
rewrite (pred_addZ_r (multZ (pos n0) (predZ y)) y).
elim (pred_addZ_l (multZ (pos n0) (predZ y)) y).
elim (addZ_commutativity y (multZ (pos n0) y)).
elim (addZ_associativity y (multZ (pos n0) y) (neg (S n0))).
elim (addZ_commutativity (addZ (multZ (pos n0) y) (neg (S n0))) y).
rewrite H; elim (pred_addZ_r (multZ (pos n0) y) (oppZ (pos n0))).
reflexivity.
simple induction n.
simpl in |- *.
replace (pos 0) with IZ; auto.
rewrite (add_IZ_succZ (oppZ y)).
exact (opp_predZ y).
intros n0 H; do 2 rewrite (tech_mult_negZ n0).
rewrite H; rewrite (opp_predZ y).
elim (addZ_commutativity (oppZ (neg n0)) (multZ (neg n0) y)).
elim (addZ_associativity (oppZ (neg n0)) (multZ (neg n0) y) (succZ (oppZ y))).
elim (addZ_commutativity (addZ (multZ (neg n0) y) (succZ (oppZ y))) (oppZ (neg n0))).
rewrite (succ_addZ_r (multZ (neg n0) y) (oppZ y)).
rewrite (succ_addZ_l (addZ (multZ (neg n0) y) (oppZ y)) (oppZ (neg n0))).
elim (succ_addZ_r (addZ (multZ (neg n0) y) (oppZ y)) (oppZ (neg n0))).
Admitted.

Lemma mult_OZ : forall x : Z, multZ x OZ = OZ.
simple destruct x.
reflexivity.
simple induction n.
reflexivity.
intros y H; rewrite (tech_mult_posZ y OZ); rewrite H; reflexivity.
simple induction n.
reflexivity.
Admitted.

Lemma mult_IZ : forall x : Z, multZ x IZ = x.
simple destruct x.
reflexivity.
simple induction n.
reflexivity.
intros y H; rewrite (tech_mult_posZ y IZ); rewrite H.
rewrite (add_IZ_succZ (pos y)); reflexivity.
simple induction n.
reflexivity.
intros y H; rewrite (tech_mult_negZ y IZ); rewrite H; unfold IZ in |- *; unfold oppZ in |- *.
Admitted.

Lemma mult_mIZ : forall x : Z, multZ x (neg 0) = oppZ x.
simple destruct x.
reflexivity.
simple induction n.
reflexivity.
intros y H; rewrite (tech_mult_posZ y (neg 0)); rewrite H.
rewrite (add_mIZ_predZ (oppZ (pos y))); reflexivity.
simple induction n.
reflexivity.
intros y H; rewrite (tech_mult_negZ y (neg 0)); rewrite H.
elim (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (neg y) (neg 0) I I).
Admitted.

Theorem multZ_commutativity : commutativity Z multZ.
unfold commutativity in |- *; intros; elim x.
rewrite (mult_OZ y); unfold multZ in |- *; reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; exact (mult_IZ y).
intros y0 H; rewrite (tech_mult_posZ y0 y); rewrite H.
elim (mult_succZ_r y (pos y0)); unfold succZ in |- *; reflexivity.
intros; elim n.
simpl in |- *; symmetry in |- *; exact (mult_mIZ y).
intros y0 H; rewrite (tech_mult_negZ y0 y); rewrite H.
Admitted.

Lemma multZ_eq3 : forall (n1 : nat) (n : Z), multZ (pos (S n1)) n = addZ (multZ (pos n1) n) n.
Proof.
auto.
