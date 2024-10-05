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

Theorem gauss : forall (d a b:nat),(rel_prime a d)->(divides (a*b) d)->(divides b d).
unfold rel_prime.
intros.
elim (bezout 1 a d H);intro u;intro.
elim H1;intro v;intro.
elim H0;intro q;intro.
case H2;intro;[exists (q*u-b*v) | exists (b*v-q*u)];rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;rewrite <- H3;rewrite (mult_comm a b);rewrite (mult_comm d b);rewrite <- mult_assoc;rewrite <- mult_assoc;rewrite <- mult_minus_lemma2;rewrite <- H4;auto with arith.
