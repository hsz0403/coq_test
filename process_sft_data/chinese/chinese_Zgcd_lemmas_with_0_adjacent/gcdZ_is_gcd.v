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

Lemma gcdZ_is_gcd : forall a b d : Z, is_gcdZ a b d -> is_gcd Z IdZ multZ OZ a b d.
intros.
elim H; intros.
apply (gcd_OZ_absZ b0).
unfold is_gcd in |- *.
split.
elim H3; intros; elim H5; intros; exact H6.
split.
elim H1; intros; elim H5; intros; elim H7; intros; rewrite H9.
apply (div_add Z IdZ addZ multZ OZ oppZ Z_ring (multZ b0 q) r d0).
elim H3; intros; elim H11; intros.
exact (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b0 q d0 H12 I).
elim H3; intros; exact H10.
intros.
elim H3; intros; elim H7; intros.
apply (H9 q0).
cut (r = addZ a0 (oppZ (multZ b0 q))); intros.
rewrite H10.
apply (div_add Z IdZ addZ multZ OZ oppZ Z_ring a0 (oppZ (multZ b0 q)) q0 H5).
apply (div_opp Z IdZ addZ multZ OZ oppZ Z_ring (multZ b0 q) q0).
exact (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b0 q q0 H4 I).
elim H1; intros; elim H11; intros; elim H13; intros; rewrite H15.
elim (addZ_commutativity r (multZ b0 q)).
elim (addZ_associativity r (multZ b0 q) (oppZ (multZ b0 q))).
elim (addZ_opposite (multZ b0 q) I); intros.
elim H17; intros.
elim H19; intros.
rewrite H20.
symmetry in |- *.
exact (add_OZ r).
exact H4.
