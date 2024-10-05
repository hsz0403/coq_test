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

Lemma rel_prime_mult : forall (a b c:nat),(rel_prime a b)->(rel_prime a c)->(rel_prime a (b*c)).
intros.
split.
split;try (apply one_min_div).
intros.
elim H1;intros.
case (rel_prime_dec b d');intro.
assert (divides c d').
apply gauss with b;trivial.
elim H0;intros.
apply H6;unfold is_cd;tauto.
generalize (gcd_is_gcd b d');intro.
assert ((gcd b d')<>1).
intro;apply n.
unfold rel_prime;rewrite <- H5;trivial.
generalize (gcd_div_l (gcd b d') b d' H4);intro.
generalize (gcd_div_r (gcd b d') b d' H4);intro.
assert (divides a (gcd b d')).
apply divides_trans with d';[apply H2 | apply H7].
elim H5.
apply divides_antisym.
apply one_min_div.
elim H;intros;apply H10;unfold is_cd;tauto.
