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

Lemma unicity_is_gcdZ : forall a b d1 d2 : Z, is_gcdZ a b d1 -> is_gcdZ a b d2 -> d2 = d1.
intros.
elim (gcd_unicity_apart_sign a b d1 d2 (gcdZ_is_gcd a b d1 H) (gcdZ_is_gcd a b d2 H0)).
intros; exact H1.
intros; apply (le_opp_OZ2 d2 d1 H1 (positive_is_gcdZ a b d2 H0) (positive_is_gcdZ a b d1 H)).
