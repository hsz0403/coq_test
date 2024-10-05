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

Lemma gcdZ_is_gcd : forall a b d : Z, is_gcdZ a b d -> is_gcd Z IdZ Zmult 0%Z a b d.
Proof.
intros.
elim H.
intros.
apply (gcd_OZ_absZ b0).
clear H a b d; intros.
unfold is_gcd in |- *.
elim H3; clear H3; intros.
elim H4; clear H4; intros.
split.
exact H4.
split.
rewrite H1.
apply (div_add Z IdZ Zplus Zmult 0%Z Z.opp Z_ring (b * q)%Z r d).
apply (div_mult Z IdZ Zplus Zmult 0%Z Z.opp Z_ring b q d).
exact H4.
exact I.
exact H3.
intros.
apply (H5 q0).
cut (r = (a - b * q)%Z); intros.
rewrite H8.
apply (div_add Z IdZ Zplus Zmult 0%Z Z.opp Z_ring a (- (b * q))%Z q0 H7).
apply (div_opp Z IdZ Zplus Zmult 0%Z Z.opp Z_ring (b * q)%Z q0).
exact (div_mult Z IdZ Zplus Zmult 0%Z Z.opp Z_ring b q q0 H6 I).
rewrite H1; auto with zarith.
exact H6.
