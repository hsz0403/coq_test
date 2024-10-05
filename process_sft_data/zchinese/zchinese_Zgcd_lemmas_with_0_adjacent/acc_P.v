Require Export misc.
Require Export Zstruct.
Require Export ZArith.
Require Import Omega.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Unset Standard Proposition Elimination Names.
Inductive is_gcdZ : Z -> Z -> Z -> Prop := | gcd_OZ : forall b : Z, is_gcdZ 0%Z b (Z.abs b) | gcd_mod : forall b a d q r : Z, b <> 0%Z -> (0 <= r < Z.abs b)%Z -> a = (b * q + r)%Z -> is_gcdZ r b d -> is_gcdZ b a d.
Definition have_gcdZ (a b : Z) := {d : Z | is_gcdZ a b d}.
Definition gcdZ_i (a b : Z) := exist (is_gcdZ a b).
Definition P (a : Z) := forall b : Z, have_gcdZ a b.
Definition gcdZ (a b : Z) := pi1 Z (is_gcdZ a b) (gcdZ_exists a b).
Inductive verify_BezoutZ (a b : Z) : Set := Bezout_i : forall u v : Z, (a * u + b * v)%Z = gcdZ a b -> verify_BezoutZ a b.
Definition Q (a : Z) := forall b : Z, verify_BezoutZ a b.
Definition congruentZ (x y n : Z) := divide Z IdZ Zmult 0%Z n (x + - y)%Z.

Lemma acc_P : forall n : Z, (forall m : Z, (Z.abs m < Z.abs n)%Z -> P m) -> P n.
Proof.
intros.
case (Z_zerop n); intro.
unfold P in |- *.
intro.
split with (Z.abs b).
rewrite e.
apply (gcd_OZ b).
unfold P in |- *; intro.
elim (Zdiv_eucl_extended n0 b).
intro p; elim p; intros q r H0; elim H0; clear p H0; intros.
cut (Z.abs r < Z.abs n)%Z; intros.
elim (H r H2 n).
intros.
split with x.
apply gcd_mod with q r; trivial.
rewrite Z.abs_eq; auto with zarith.
