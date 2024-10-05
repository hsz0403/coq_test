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
apply lt_minus2; trivial.
