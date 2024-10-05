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

Lemma gcd_OZ_absZ : forall b : Z, is_gcd Z IdZ multZ OZ OZ b (absZ b).
intros.
elim (abs_eq_or_oppZ b); intro y.
rewrite y.
unfold is_gcd in |- *; split.
unfold divide in |- *; unfold IdZ in |- *; split.
exact I.
split.
exact I.
left; reflexivity.
split; unfold divide in |- *; unfold IdZ in |- *.
split.
exact I.
split.
exact I.
elim (eq_OZ_dec b); intro y0.
left; exact y0.
right.
split.
exact y0.
exists IZ.
split.
exact I.
symmetry in |- *; exact (mult_IZ b).
intros; exact H0.
rewrite y.
unfold is_gcd in |- *; split.
unfold divide in |- *; unfold IdZ in |- *; split.
exact I.
split.
exact I.
left; reflexivity.
split; unfold divide in |- *; unfold IdZ in |- *; split.
exact I.
split.
exact I.
elim (eq_OZ_dec b); intro y0.
left; exact y0.
right.
split.
unfold not in |- *; intros; elim y0.
exact (opp_O Z IdZ addZ multZ OZ oppZ Z_ring b I H).
exists (oppZ IZ); split.
exact I.
rewrite (mult_opp_opp Z IdZ addZ multZ OZ oppZ Z_ring b IZ I I).
symmetry in |- *; exact (mult_IZ b).
exact I.
split.
exact I.
elim H0; intros; elim H2; intros; elim H4; intros.
rewrite H5.
left; reflexivity.
right; split.
elim H5; intros; exact H6.
elim H5; intros; elim H7; intros.
exists (oppZ x).
split.
exact I.
elim H8; intros; rewrite H10.
symmetry in |- *; exact (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring q x I I).
