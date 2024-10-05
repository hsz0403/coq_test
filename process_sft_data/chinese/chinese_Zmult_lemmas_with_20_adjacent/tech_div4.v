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

Theorem mult_add_distributivity : distributivity Z addZ multZ.
unfold distributivity in |- *; intros; case x.
split; reflexivity.
simple induction n.
split.
rewrite addZ_eq2; rewrite multZ_eq2.
rewrite (mult_succZ_l y z); exact (addZ_commutativity (multZ y z) z).
reflexivity.
intros y0 H.
elim H; intros; split.
rewrite addZ_eq3; rewrite multZ_eq3.
rewrite mult_succZ_l; rewrite H0.
elim (addZ_associativity (multZ (pos y0) z) (multZ y z) z).
elim (addZ_commutativity z (multZ y z)).
apply addZ_associativity.
do 3 rewrite multZ_eq3.
rewrite H1.
apply (add_add Z addZ addZ_commutativity addZ_associativity).
simple induction n.
split.
rewrite addZ_eq4; rewrite multZ_eq4; rewrite (mult_predZ_l y z).
exact (addZ_commutativity (multZ y z) (oppZ z)).
rewrite multZ_eq4.
apply (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity y z I I).
intros y0 H.
split.
rewrite (tech_add_neg_predZ y0 y); rewrite (mult_predZ_l (addZ (neg y0) y) z).
elim H; intros.
rewrite H0.
elim (addZ_associativity (multZ (neg y0) z) (multZ y z) (oppZ z)).
elim (addZ_commutativity (oppZ z) (multZ y z)).
rewrite (addZ_associativity (multZ (neg y0) z) (oppZ z) (multZ y z)).
elim (tech_mult_negZ y0 z); reflexivity.
rewrite (tech_mult_negZ y0 (addZ y z)); rewrite (tech_mult_negZ y0 y).
rewrite (tech_mult_negZ y0 z); elim H; intros; rewrite H1.
elim (add_add Z addZ addZ_commutativity addZ_associativity (multZ (neg y0) y) (multZ (neg y0) z) (oppZ y) (oppZ z)).
elim (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity y z I I).
Admitted.

Lemma mult_oppZ_r : forall x y : Z, multZ x (oppZ y) = oppZ (multZ x y).
intros; case x.
reflexivity.
simple induction n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos y0) y) y I I).
elim H; reflexivity.
intros; elim n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (neg y0) y) (oppZ y) I I).
Admitted.

Lemma mult_oppZ_l : forall x y : Z, multZ (oppZ x) y = oppZ (multZ x y).
simple destruct y.
rewrite (mult_OZ (oppZ x)); rewrite (mult_OZ x); reflexivity.
intros; elim (multZ_commutativity (pos n) (oppZ x)).
elim (multZ_commutativity (pos n) x); elim n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; symmetry in |- *.
exact (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos y0) x) x I I).
intros; elim (multZ_commutativity (neg n) (oppZ x)).
elim (multZ_commutativity (neg n) x); elim n.
reflexivity.
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite H; symmetry in |- *.
Admitted.

Lemma tech_mult_pos_posZ : forall n m : nat, multZ (pos n) (pos m) = pos (n * m + (n + m)).
intros; elim n.
reflexivity.
intros y H; rewrite (tech_mult_posZ y (pos m)); rewrite H.
rewrite (tech_add_pos_posZ (y * m + (y + m)) m).
Admitted.

Lemma tech_mult_neg_negZ : forall n m : nat, multZ (neg n) (neg m) = pos (n * m + (n + m)).
intros; elim n.
reflexivity.
intros y H; rewrite (tech_mult_negZ y (neg m)); rewrite H; unfold oppZ in |- *.
rewrite (tech_add_pos_posZ (y * m + (y + m)) m).
Admitted.

Lemma tech_mult_pos_negZ : forall n m : nat, multZ (pos n) (neg m) = neg (n * m + (n + m)).
intros; elim n.
simpl in |- *; reflexivity.
intros y H; rewrite (tech_mult_posZ y (neg m)); rewrite H.
rewrite (tech_add_neg_negZ (y * m + (y + m)) m).
Admitted.

Lemma tech_mult_neg_posZ : forall n m : nat, multZ (neg n) (pos m) = neg (n * m + (n + m)).
intros; elim n.
simpl in |- *; reflexivity.
intros y H; rewrite (tech_mult_negZ y (pos m)); unfold oppZ in |- *; rewrite H.
rewrite (tech_add_neg_negZ (y * m + (y + m)) m).
Admitted.

Theorem multZ_associativity : associativity Z multZ.
unfold associativity in |- *; intros; elim x.
reflexivity.
simple induction n.
unfold multZ in |- *; reflexivity.
intros y0 H; do 2 rewrite (tech_mult_posZ y0).
rewrite H; elim (mult_oppZ_l y z).
elim (mult_add_distributivity (multZ (pos y0) y) y z); intros.
elim H0.
reflexivity.
simple induction n.
simpl in |- *; symmetry in |- *; exact (mult_oppZ_l y z).
intros y0 H; do 2 rewrite (tech_mult_negZ y0).
rewrite H; elim (mult_oppZ_l y z).
elim (mult_add_distributivity (multZ (neg y0) y) (oppZ y) z); intros.
elim H0.
Admitted.

Theorem Z_ring : is_ring Z IdZ addZ multZ OZ oppZ.
unfold is_ring in |- *.
split.
exact addZ_commutativity.
split.
exact Z_group.
split.
unfold intern in |- *.
intros.
exact I.
split.
exact multZ_associativity.
Admitted.

Theorem Z_unitary_commutative_ring : is_unitary_commutative_ring Z IdZ addZ multZ OZ IZ oppZ.
unfold is_unitary_commutative_ring in |- *.
split.
exact Z_ring.
split.
exact multZ_commutativity.
Admitted.

Lemma tech_integ_posZ : forall (n : nat) (x : Z), multZ (pos n) x = OZ -> x = OZ.
intros n x; elim x.
reflexivity.
intros n0; rewrite (tech_mult_pos_posZ n n0); intros.
absurd (pos (n * n0 + (n + n0)) = OZ).
discriminate.
exact H.
intros n0; rewrite (tech_mult_pos_negZ n n0); intros.
absurd (neg (n * n0 + (n + n0)) = OZ).
discriminate.
Admitted.

Lemma tech_integ_negZ : forall (n : nat) (x : Z), multZ (neg n) x = OZ -> x = OZ.
intros n x; elim x.
reflexivity.
intros n0; rewrite (tech_mult_neg_posZ n n0); intros.
absurd (neg (n * n0 + (n + n0)) = OZ).
discriminate.
exact H.
intros n0; rewrite (tech_mult_neg_negZ n n0); intros.
absurd (pos (n * n0 + (n + n0)) = OZ).
discriminate.
Admitted.

Theorem integrityZ : integrity Z multZ OZ.
unfold integrity in |- *; intros a b; elim a.
intros; left; reflexivity.
intros; right; apply (tech_integ_posZ n b); exact H.
Admitted.

Lemma tech_mult_pos_succZ : forall n m : nat, posOZ (S n * S m) = multZ (pos n) (pos m).
intros; elim m.
elim multZ_neutral; intros; elim (H0 (pos n) I); intros.
replace (pos 0) with IZ; auto.
rewrite H1.
elim (mult_commut 1 (S n)).
rewrite (mult_neutr (S n)).
unfold posOZ in |- *; reflexivity.
intros y H; elim (multZ_commutativity (pos (S y)) (pos n)).
rewrite (tech_mult_posZ y (pos n)); elim (multZ_commutativity (pos n) (pos y)).
elim H; elim (mult_n_Sm (S n) (S y)); elim (plus_n_Sm (S n * S y) n).
elim (mult_n_Sm (S n) y); elim (plus_n_Sm (S n * y) n).
unfold posOZ in |- *; rewrite (tech_add_pos_posZ (S n * y + n) n).
Admitted.

Lemma tech_mult_pos_succZ2 : forall n m : nat, multZ (pos n) (pos m) = pos (S n * m + n).
intros; elim (tech_mult_pos_succZ n m).
Admitted.

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
Admitted.

Lemma tech_div2 : forall n0 n q : nat, S n0 = q * S n -> neg n0 = multZ (pos n) (negOZ q).
intros n0 n q; elim q.
simpl in |- *; intros; absurd (S n0 = 0).
discriminate.
exact H.
intros y H; unfold negOZ in |- *.
rewrite (tech_mult_pos_negZ n y); intros.
simpl in H0; rewrite (eq_add_S _ _ H0).
elim (mult_commut (S n) y); simpl in |- *; elim (plus_comm (n + y) (n * y)).
Admitted.

Lemma tech_div31 : forall n q : nat, addZ (oppZ (multZ (pos n) (pos q))) (pos n) = oppZ (multZ (pos n) (posOZ q)).
intros; elim q.
unfold posOZ in |- *; rewrite (mult_OZ (pos n)).
cut (IZ = pos 0); intros.
elim H.
rewrite (mult_IZ (pos n)).
elim (addZ_opposite (pos n) I); intros; elim H1; intros; elim H3; intros.
rewrite H5; reflexivity.
reflexivity.
intros y H; unfold posOZ in |- *; elim (multZ_commutativity (pos (S y)) (pos n)).
rewrite (tech_mult_posZ y (pos n)).
rewrite (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos y) (pos n)) (pos n) I I).
elim (addZ_associativity (oppZ (multZ (pos y) (pos n))) (oppZ (pos n)) (pos n)).
elim (addZ_opposite (pos n) I); intros; elim H1; intros; elim H3; intros.
rewrite H5; rewrite (add_OZ (oppZ (multZ (pos y) (pos n)))).
Admitted.

Lemma tech_div32 : forall n q r : nat, S n > r -> pos (n - r) = addZ (pos n) (oppZ (posOZ r)).
intros n q r; elim r.
unfold posOZ in |- *; unfold oppZ in |- *; rewrite (add_OZ (pos n)); elim (minus_n_O n).
reflexivity.
intros y H; unfold posOZ in |- *; unfold oppZ in |- *; symmetry in |- *.
Admitted.

Lemma tech_div3 : forall n0 n q r : nat, S n0 = q * S n + r -> S n > r -> neg n0 = addZ (multZ (pos n) (neg q)) (pos (n - r)).
intros.
elim (tech_opp_pos_negZ q); intros; elim H1.
rewrite (mult_oppZ_r (pos n) (pos q)); rewrite (tech_div32 n q r H0).
rewrite (addZ_associativity (oppZ (multZ (pos n) (pos q))) (pos n) (oppZ (posOZ r))) .
rewrite (tech_div31 n q).
elim (opp_add Z IdZ addZ OZ oppZ Z_group addZ_commutativity (multZ (pos n) (posOZ q)) (posOZ r) I I).
Admitted.

Lemma tech_div5 : forall n0 n q : nat, S n0 = q * S n -> neg n0 = multZ (neg n) (posOZ q).
intros; cut (posOZ q = oppZ (negOZ q)); intros.
rewrite H0.
elim (tech_opp_pos_negZ n); intros; elim H1.
rewrite (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring (pos n) (negOZ q) I I).
exact (tech_div2 n0 n q H).
Admitted.

Lemma tech_div6 : forall n0 n q r : nat, S n0 = q * S n + r -> S n > r -> neg n0 = addZ (multZ (neg n) (pos q)) (pos (n - r)).
intros.
elim (tech_opp_pos_negZ q); intros; elim H2.
elim (tech_opp_pos_negZ n); intros; elim H3.
rewrite (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring (pos n) (neg q) I I).
Admitted.

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
Admitted.

Lemma sgn_abs : forall x : Z, multZ x (sgnZ x) = absZ x.
simple destruct x.
reflexivity.
intros; exact (mult_IZ (pos n)).
Admitted.

Lemma tech_div4 : forall n0 n q r : nat, S n0 = q * S n + r -> pos n0 = addZ (multZ (neg n) (negOZ q)) (posOZ r).
intros; cut (multZ (neg n) (negOZ q) = multZ (pos n) (posOZ q)); intros.
rewrite H0; intros; exact (tech_div1 n0 n q r H).
cut (negOZ q = oppZ (posOZ q)); intros.
rewrite H0.
elim (tech_opp_pos_negZ n); intros; elim H1.
apply (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring (pos n) (posOZ q) I I).
elim q; reflexivity.
