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

Lemma power_power_rel_prime : forall (a n b m:nat),(n>0)->(m>0)->((rel_prime (power a n) (power b m))<->(rel_prime a b)).
split;intro.
apply power_rel_prime with m;trivial;apply rel_prime_sym;apply power_rel_prime with n;trivial;apply rel_prime_sym;trivial.
apply rel_prime_power;apply rel_prime_sym;apply rel_prime_power;apply rel_prime_sym;trivial.
