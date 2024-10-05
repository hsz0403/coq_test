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

Lemma gcd_rel_prime : forall (d a b:nat)(H:(is_gcd d a b)),(d <> O)->(rel_prime (quo a d (gcd_div_l d a b H)) (quo b d (gcd_div_r d a b H))).
unfold rel_prime.
intros.
generalize (quo_is_quo a d (gcd_div_l d a b H));intro.
generalize (quo_is_quo b d (gcd_div_r d a b H));intro.
unfold is_gcd;split;unfold is_cd.
split;apply one_min_div.
intros.
elim H3;intros.
elim H4;intro q;intro.
elim H5;intro q';intro.
rewrite H6 in H1.
rewrite H7 in H2.
assert (divides d (d*d')).
red in H;elim H;intros.
apply H9;red;split;[exists q;rewrite H1;ring | exists q';rewrite H2;ring].
elim H8;intros.
exists x.
apply mult_lemma6 with d;trivial.
rewrite mult_assoc;rewrite <- H9;auto with arith.
