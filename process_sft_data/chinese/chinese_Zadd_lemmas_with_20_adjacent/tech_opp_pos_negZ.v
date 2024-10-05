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

Lemma add_mIZ_predZ : forall x : Z, addZ x (neg 0) = predZ x.
intros.
cut (predZ OZ = neg 0); intros.
elim H.
rewrite (pred_addZ_r x OZ); rewrite (add_OZ x); reflexivity.
Admitted.

Theorem addZ_commutativity : commutativity Z addZ.
unfold commutativity in |- *; intros; elim x.
simpl in |- *; symmetry in |- *; exact (add_OZ y).
simple induction n.
simpl in |- *; symmetry in |- *; exact (add_IZ_succZ y).
intros; rewrite (tech_add_pos_succZ n0 y).
rewrite H.
cut (succZ (pos n0) = pos (S n0)); intros.
elim H0.
rewrite (succ_addZ_r y (pos n0)); reflexivity.
reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; exact (add_mIZ_predZ y).
intros; rewrite (tech_add_neg_predZ n0 y).
rewrite H.
cut (predZ (neg n0) = neg (S n0)); intros.
elim H0.
rewrite (pred_addZ_r y (neg n0)); reflexivity.
Admitted.

Lemma tech_add_pos_neg_posZ : forall n1 n2 : nat, n2 < n1 -> addZ (pos n1) (neg n2) = pos (n1 - S n2).
simple induction n2.
intros; elim (addZ_commutativity (neg 0) (pos n1)).
rewrite addZ_eq4.
elim minus_n_Sm; trivial.
elim minus_n_O.
apply tech_pred_posZ; trivial.
intros; elim (addZ_commutativity (neg (S n)) (pos n1)).
rewrite tech_add_neg_predZ.
elim (addZ_commutativity (pos n1) (neg n)).
rewrite H; auto with arith.
elim (minus_n_Sm n1 (S n) H0).
apply tech_pred_posZ.
Admitted.

Theorem addZ_associativity : associativity Z addZ.
unfold associativity in |- *; intros; elim x.
unfold addZ in |- *; reflexivity.
intros; elim n.
simpl in |- *; symmetry in |- *; exact (succ_addZ_l y z).
intros.
do 2 rewrite (tech_add_pos_succZ n0).
rewrite (succ_addZ_l (addZ (pos n0) y) z); elim H; reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; exact (pred_addZ_l y z).
intros.
do 2 rewrite (tech_add_neg_predZ n0).
Admitted.

Theorem addZ_neutral : neutral Z IdZ addZ OZ.
unfold neutral in |- *; intros.
split.
exact I.
intros.
split.
exact (add_OZ x).
Admitted.

Lemma opp_succZ : forall x : Z, oppZ (succZ x) = predZ (oppZ x).
simple destruct x.
reflexivity.
intros; reflexivity.
Admitted.

Lemma opp_predZ : forall x : Z, oppZ (predZ x) = succZ (oppZ x).
simple destruct x.
reflexivity.
simple destruct n; intros; reflexivity.
Admitted.

Lemma tech_add_pos_negZ : forall n : nat, addZ (pos n) (neg n) = OZ.
simple induction n.
reflexivity.
intros; rewrite (tech_add_pos_succZ n0).
Admitted.

Lemma tech_add_neg_posZ : forall n : nat, addZ (neg n) (pos n) = OZ.
Admitted.

Lemma tech_add_pos_posZ : forall n m : nat, addZ (pos n) (pos m) = pos (S (n + m)).
intros; elim n.
reflexivity.
Admitted.

Lemma tech_add_neg_negZ : forall n m : nat, addZ (neg n) (neg m) = neg (S (n + m)).
simple induction n.
reflexivity.
Admitted.

Theorem addZ_opposite : opposite Z IdZ addZ OZ oppZ.
repeat split; trivial.
case x.
reflexivity.
intros; exact (tech_add_pos_negZ n).
intros; exact (tech_add_neg_posZ n).
case x.
reflexivity.
intros; exact (tech_add_neg_posZ n).
Admitted.

Theorem Z_group : is_group Z IdZ addZ OZ oppZ.
split.
red in |- *; trivial.
split.
exact addZ_associativity.
split.
exact addZ_neutral.
Admitted.

Theorem abs_eq_or_oppZ : forall x : Z, {absZ x = x} + {absZ x = oppZ x}.
Admitted.

Lemma tech_opp_pos_negZ : forall n : nat, oppZ (pos n) = neg n /\ oppZ (neg n) = pos n.
simple induction n; auto with arith.
