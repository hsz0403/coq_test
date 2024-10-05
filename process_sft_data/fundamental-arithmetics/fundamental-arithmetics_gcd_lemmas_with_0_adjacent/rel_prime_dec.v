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

Lemma rel_prime_dec : forall (a b:nat),{rel_prime a b}+{~(rel_prime a b)}.
intros.
unfold rel_prime.
generalize (gcd_is_gcd a b);intro.
case (eq_nat_dec (gcd a b) 1);intro.
left;rewrite e in H;trivial.
right;intro;apply n;apply (gcd_unique (gcd a b) 1 a b);trivial.
