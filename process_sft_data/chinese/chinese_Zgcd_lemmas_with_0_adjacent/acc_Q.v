Require Export misc.
Require Export Zadd.
Require Export Zle.
Require Export Euclid.
Require Export Peano_dec.
Require Export Zrec.
Require Export Zmult.
Require Export Zdiv.
Unset Standard Proposition Elimination Names.
Inductive is_gcdZ : Z -> Z -> Z -> Prop := | gcd_OZ : forall b : Z, is_gcdZ OZ b (absZ b) | gcd_mod : forall b a d q r : Z, b <> OZ -> is_diveuclZ a b q r -> is_gcdZ r b d -> is_gcdZ b a d.
Definition have_gcdZ (a b : Z) := {d : Z | is_gcdZ a b d}.
Definition gcdZ_i (a b : Z) := exist (is_gcdZ a b).
Definition P (a : Z) := forall b : Z, have_gcdZ a b.
Definition gcdZ (a b : Z) := pi1 Z (is_gcdZ a b) (gcdZ_exists a b).
Inductive verify_BezoutZ (a b : Z) : Set := Bezout_i : forall u v : Z, addZ (multZ a u) (multZ b v) = gcdZ a b -> verify_BezoutZ a b.
Definition Q (a : Z) := forall b : Z, verify_BezoutZ a b.
Definition congruentZ (x y n : Z) := divide Z IdZ multZ OZ n (addZ x (oppZ y)).

Lemma acc_Q : forall n : Z, (forall m : Z, lt_absZ m n -> Q m) -> Q n.
Proof.
intros q f.
case (eq_OZ_dec q); intro.
unfold Q in |- *; intro b.
split with IZ (sgnZ b).
rewrite e.
simpl in |- *.
rewrite (sgn_abs b).
apply (gcdZ_is_gcdZ OZ b (absZ b)); apply gcd_OZ.
unfold Q in |- *; intro b.
elim (divZ b q).
intros div rem; intros.
cut (lt_absZ rem q); intros.
elim (f rem H q).
intros.
split with (addZ v (oppZ (multZ div u))) u.
elim i.
intros.
elim H1.
intros.
elim H3.
intros.
pattern b at 1 in |- *.
rewrite H5.
elim (mult_add_distributivity q v (oppZ (multZ div u))); intros.
rewrite H7.
elim (mult_add_distributivity (multZ q div) rem u); intros.
rewrite H8.
rewrite (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring q (multZ div u) I I).
elim (addZ_commutativity (multZ rem u) (multZ (multZ q div) u)).
rewrite (add_add Z addZ addZ_commutativity addZ_associativity (multZ q v) (oppZ (multZ q (multZ div u))) (multZ rem u) (multZ (multZ q div) u)).
elim (addZ_commutativity (multZ rem u) (multZ q v)).
rewrite e.
elim (multZ_associativity q div u).
elim (addZ_opposite (multZ q (multZ div u)) I); intros.
elim H11; intros; elim H13; intros.
rewrite H15.
rewrite (add_OZ (gcdZ rem q)).
exact (gcd_modZ b q div rem n i).
unfold lt_absZ in |- *.
elim i; intros; elim H0; intros.
rewrite (tech_le_pos_abs rem H1).
elim H2; trivial.
exact n.
