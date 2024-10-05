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

Lemma gcd_mult : forall (d a b:nat),(is_gcd d a b)->(forall (n:nat),(is_gcd (n*d) (n*a) (n*b))).
unfold is_gcd;unfold is_cd.
intros.
elim H;intros.
elim H0;intros.
split.
elim H2;intro q;intro.
elim H3;intro q';intro.
rewrite H4;rewrite mult_assoc.
rewrite H5;rewrite mult_assoc.
split;[exists q;trivial | exists q';trivial].
intros.
elim H4;intros.
elim (bezout d a b);try (unfold is_gcd;unfold is_cd;trivial).
intro u;intro.
elim H7;intro v;intro.
elim H5;intro q;intro.
elim H6;intro q';intro.
case H8;intro;[exists (q*u-q'*v) | exists (q'*v-q*u)];rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;rewrite <- H9;rewrite <- H10;rewrite H11;rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;trivial.
