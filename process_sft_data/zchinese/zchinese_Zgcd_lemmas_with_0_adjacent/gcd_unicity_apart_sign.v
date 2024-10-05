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

Lemma gcd_unicity_apart_sign : forall a b c d : Z, is_gcd Z IdZ Zmult 0%Z a b c -> is_gcd Z IdZ Zmult 0%Z a b d -> d = c \/ d = (- c)%Z.
Proof.
intros.
elim (gcd_unicity_apart_unities Z IdZ Zplus Zmult 0%Z 1%Z Z.opp Z_unitary_commutative_ring integrityZ a b c d H H0).
intros.
elim (inversibleZ x); intros.
left.
elim H1; intros; elim H4; intros.
rewrite H6.
rewrite H2; auto with zarith.
right.
elim H1; intros; elim H4; intros.
rewrite H6.
rewrite H2; auto with zarith.
elim H1; intros; exact H2.
