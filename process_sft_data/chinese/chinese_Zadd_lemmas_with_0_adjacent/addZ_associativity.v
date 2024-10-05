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
rewrite (pred_addZ_l (addZ (neg n0) y) z); elim H; reflexivity.
