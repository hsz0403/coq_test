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

Theorem bezout_rel_prime : forall (a b:nat),(rel_prime a b)<->(exists u:nat, exists v:nat, 1=a*u-b*v \/ 1 = b*v-a*u).
intros.
unfold rel_prime.
split;intro.
apply bezout;trivial.
elim H;intro u;intro H0.
elim H0;intro v;intro.
unfold is_gcd;unfold is_cd.
split.
split;apply one_min_div.
intros.
elim H2;intros.
elim H3;intro q;intro.
elim H4;intro q';intro.
rewrite H5 in H1;rewrite H6 in H1.
case H1;intro.
exists (q*u-q'*v);rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;trivial.
exists (q'*v-q*u);rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;trivial.
