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
reflexivity.
