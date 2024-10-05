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

Lemma acc_P : forall n : Z, (forall m : Z, lt_absZ m n -> P m) -> P n.
Proof.
intros.
case (eq_OZ_dec n); intro.
unfold P in |- *.
intro.
split with (absZ b).
rewrite e.
apply (gcd_OZ b).
unfold P in |- *; intro.
elim (divZ b n).
intros.
cut (lt_absZ r n); intros.
elim (H r H0 n).
intros.
split with x.
apply gcd_mod with (2 := i); trivial.
inversion i.
decompose [and] H1.
unfold lt_absZ in |- *.
rewrite (tech_le_pos_abs r H2).
exact H4.
exact n0.
