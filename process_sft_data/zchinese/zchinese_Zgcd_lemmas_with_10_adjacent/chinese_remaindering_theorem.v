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

Lemma gcdZ_exists : forall a b : Z, have_gcdZ a b.
Proof.
Admitted.

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
Admitted.

Theorem gcdZ_correct : forall a b : Z, is_gcdZ a b (gcdZ a b).
Proof.
Admitted.

Lemma positive_is_gcdZ : forall a b d : Z, is_gcdZ a b d -> (0 <= d)%Z.
Proof.
Admitted.

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
Admitted.

Lemma gcdZ_is_gcdZ : forall a b d : Z, is_gcdZ a b d -> d = gcdZ a b.
Proof.
intros.
Admitted.

Lemma gcd_modZ : forall a b q r : Z, b <> 0%Z -> (0 <= r < Z.abs b)%Z -> a = (b * q + r)%Z -> gcdZ r b = gcdZ b a.
Proof.
intros.
apply (gcdZ_is_gcdZ b a (gcdZ r b)).
Admitted.

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
Admitted.

Lemma Bezout_exists : forall a b : Z, verify_BezoutZ a b.
Proof.
Admitted.

Lemma divide_selfZ : forall x : Z, divide Z IdZ Zmult 0%Z x x.
Proof.
intros.
unfold divide in |- *.
split.
exact I.
split.
exact I.
elim (Z_zerop x); intros.
left; exact a.
right; split.
exact b.
exists 1%Z.
split.
exact I.
Admitted.

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
