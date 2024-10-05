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

Lemma gcd_unicity_apart_sign : forall a b d1 d2 : Z, is_gcd Z IdZ multZ OZ a b d1 -> is_gcd Z IdZ multZ OZ a b d2 -> d2 = d1 \/ d2 = oppZ d1.
intros.
elim (gcd_unicity_apart_unities Z IdZ addZ multZ OZ IZ oppZ Z_unitary_commutative_ring integrityZ a b d1 d2 H H0).
intros.
elim (inversibleZ x); intros.
left.
elim H1; intros; elim H4; intros.
rewrite H6.
rewrite H2.
exact (mult_IZ d1).
right.
elim H1; intros; elim H4; intros.
rewrite H6.
rewrite H2.
simpl in |- *; exact (mult_mIZ d1).
elim H1; intros; exact H2.
