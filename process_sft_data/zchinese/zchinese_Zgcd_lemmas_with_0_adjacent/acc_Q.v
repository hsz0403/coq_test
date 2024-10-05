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

Lemma acc_Q : forall n : Z, (forall m : Z, (Z.abs m < Z.abs n)%Z -> Q m) -> Q n.
Proof.
intros q f.
elim (Z_zerop q); intro e.
unfold Q in |- *; intro b.
split with 1%Z (Z.sgn b).
rewrite e.
simpl in |- *.
rewrite (Zsgn_Zabs b).
apply (gcdZ_is_gcdZ 0 b (Z.abs b)); apply gcd_OZ.
unfold Q in |- *; intro b.
elim (Zdiv_eucl_extended e b).
intro p; elim p; clear p.
intros div r; intros.
cut (Z.abs r < Z.abs q)%Z; intros.
elim (f r H q).
intros.
split with (v + - (div * u))%Z u.
elim p.
intros.
elim H1.
intros.
intros.
pattern b at 1 in |- *.
rewrite H0; auto with zarith.
rewrite <- (gcd_modZ b q div r); auto with zarith.
rewrite <- e0.
ring.
elim p; intros; elim H0; intros.
rewrite Z.abs_eq; auto with zarith.
