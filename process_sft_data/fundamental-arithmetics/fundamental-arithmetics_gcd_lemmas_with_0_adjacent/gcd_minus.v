Require Import missing.
Require Import division.
Require Import euclide.
Require Import power.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition is_cd (d a b : nat) := (divides a d)/\(divides b d).
Definition is_gcd (d a b:nat) := (is_cd d a b)/\(forall (d':nat),(is_cd d' a b)->(divides d d')).
Definition f (x:nat*nat) := (fst x)+(snd x).
Definition R (x y:nat*nat) := (f x)<(f y).
Definition gcd (a b:nat) := let (d,_):=(gcd_exists a b) in d.
Definition rel_prime (a b:nat) := (is_gcd 1 a b).

Lemma gcd_minus : forall (d a b:nat),(a <= b)->((is_gcd d a b)<->(is_gcd d a (b-a))).
intros.
unfold is_gcd.
split;intro.
elim H0;intros.
split.
red in H1;red.
elim H1;intros.
split;try tauto.
apply divides_minus;trivial.
unfold is_cd;intros.
apply H2;red;elim H3;intros.
split;[tauto | rewrite (le_plus_minus a b H);apply divides_plus;trivial].
elim H0;unfold is_cd;intros.
split.
split;[tauto | elim H1;intros;rewrite (le_plus_minus a b H);apply divides_plus;trivial].
intros.
elim H3;intros;apply H2.
split;try (apply divides_minus);trivial.
