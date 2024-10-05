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

Lemma unicity_is_gcdZ : forall a b c d : Z, is_gcdZ a b c -> is_gcdZ a b d -> d = c.
Proof.
intros.
elim (gcd_unicity_apart_sign a b c d (gcdZ_is_gcd a b c H) (gcdZ_is_gcd a b d H0)).
intros; exact H1.
intros.
cut (d = 0%Z).
intro eq; rewrite eq; rewrite eq in H1; auto with zarith.
apply Zle_antisym.
rewrite H1; set (c_pos := positive_is_gcdZ a b c H) in *.
omega.
set (d_pos := positive_is_gcdZ a b d H0) in *.
auto with zarith.
