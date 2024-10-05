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

Theorem chinese_remaindering_theorem : forall a b x y : Z, gcdZ a b = 1%Z -> {z : Z | congruentZ z x a /\ congruentZ z y b}.
Proof.
intros.
elim (Bezout_exists a b); intros.
exists (x * (b * v) + y * (a * u))%Z.
unfold congruentZ in |- *; split.
rewrite H in e.
replace (x * (b * v) + y * (a * u) + - x)%Z with (a * (u * (y - x)))%Z.
unfold divide in |- *.
split.
exact I.
split.
exact I.
elim (Z_zerop a); intros.
left; rewrite a0; auto with zarith.
right; split; trivial; exists (u * (y - x))%Z; auto with zarith.
split.
exact I.
reflexivity.
replace (b * v)%Z with (1 + - (a * u))%Z; auto with zarith.
ring.
rewrite H in e.
replace (x * (b * v) + y * (a * u) + - y)%Z with (b * (v * (x - y)))%Z.
unfold divide in |- *.
split.
exact I.
split.
exact I.
elim (Z_zerop b); intros.
left; rewrite a0; auto with zarith.
right; split; trivial; exists (v * (x - y))%Z; auto with zarith.
split.
exact I.
reflexivity.
replace (a * u)%Z with (1 + - (b * v))%Z; auto with zarith.
ring.
