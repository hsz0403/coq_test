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

Theorem chinese_remaindering_theorem : forall a b x y : Z, gcdZ a b = IZ -> {z : Z | congruentZ z x a /\ congruentZ z y b}.
intros.
elim (Bezout_exists a b); intros.
exists (addZ (multZ x (multZ b v)) (multZ y (multZ a u))).
unfold congruentZ in |- *; split.
replace (multZ b v) with (addZ IZ (oppZ (multZ a u))).
elim (mult_add_distributivity x IZ (oppZ (multZ a u))); intros.
rewrite H1; clear H0 H1.
rewrite (mult_IZ x).
elim (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring a u I I).
rewrite (multZ_associativity x a (oppZ u)).
elim (multZ_commutativity a x).
elim (multZ_associativity a x (oppZ u)).
rewrite (multZ_associativity y a u).
elim (multZ_commutativity a y).
elim (multZ_associativity a y u).
elim (addZ_associativity x (multZ a (multZ x (oppZ u))) (multZ a (multZ y u))).
elim (addZ_commutativity (addZ (multZ a (multZ x (oppZ u))) (multZ a (multZ y u))) x).
elim (addZ_associativity (addZ (multZ a (multZ x (oppZ u))) (multZ a (multZ y u))) x (oppZ x)).
elim (addZ_opposite x I); intros.
elim H1; intros.
elim H3; intros.
rewrite H4; clear H0 H1 H2 H3 H4 H5.
rewrite (add_OZ (addZ (multZ a (multZ x (oppZ u))) (multZ a (multZ y u)))).
apply (div_add Z IdZ addZ multZ OZ oppZ Z_ring (multZ a (multZ x (oppZ u))) (multZ a (multZ y u)) a).
apply (div_mult Z IdZ addZ multZ OZ oppZ Z_ring a (multZ x (oppZ u)) a (divide_selfZ a) I).
apply (div_mult Z IdZ addZ multZ OZ oppZ Z_ring a (multZ y u) a (divide_selfZ a) I).
elim H.
elim e.
elim (addZ_commutativity (multZ b v) (multZ a u)).
elim (addZ_associativity (multZ b v) (multZ a u) (oppZ (multZ a u))).
elim (addZ_opposite (multZ a u) I); intros.
elim H1; intros.
elim H3; intros.
rewrite H4; clear H0 H1 H2 H3 H4 H5.
exact (add_OZ (multZ b v)).
cut (multZ a u = addZ IZ (oppZ (multZ b v))); intros.
rewrite H0; clear H0.
elim (mult_add_distributivity y IZ (oppZ (multZ b v))); intros.
rewrite H1; clear H0 H1.
rewrite (mult_IZ y).
elim (mult_opp_r Z IdZ addZ multZ OZ oppZ Z_ring b v I I).
rewrite (multZ_associativity y b (oppZ v)).
elim (multZ_commutativity b y).
elim (multZ_associativity b y (oppZ v)).
rewrite (multZ_associativity x b v).
elim (multZ_commutativity b x).
elim (multZ_associativity b x v).
elim (addZ_commutativity (multZ b (multZ y (oppZ v))) y).
rewrite (addZ_associativity (multZ b (multZ x v)) (multZ b (multZ y (oppZ v))) y) .
elim (addZ_associativity (addZ (multZ b (multZ x v)) (multZ b (multZ y (oppZ v)))) y (oppZ y)).
elim (addZ_opposite y I); intros.
elim H1; intros.
elim H3; intros.
rewrite H4; clear H0 H1 H2 H3 H4 H5.
rewrite (add_OZ (addZ (multZ b (multZ x v)) (multZ b (multZ y (oppZ v))))).
apply (div_add Z IdZ addZ multZ OZ oppZ Z_ring (multZ b (multZ x v)) (multZ b (multZ y (oppZ v))) b).
apply (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b (multZ x v) b (divide_selfZ b) I).
apply (div_mult Z IdZ addZ multZ OZ oppZ Z_ring b (multZ y (oppZ v)) b (divide_selfZ b) I).
elim H.
elim e.
elim (addZ_associativity (multZ a u) (multZ b v) (oppZ (multZ b v))).
elim (addZ_opposite (multZ b v) I); intros.
elim H1; intros.
elim H3; intros.
rewrite H4; clear H0 H1 H2 H3 H4 H5.
symmetry in |- *; exact (add_OZ (multZ a u)).
