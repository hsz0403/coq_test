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

Lemma tech_opp_pos_negZ : forall n : nat, oppZ (pos n) = neg n /\ oppZ (neg n) = pos n.
Admitted.

Theorem abs_eq_or_oppZ : forall x : Z, {absZ x = x} + {absZ x = oppZ x}.
simple destruct x; auto with arith.
