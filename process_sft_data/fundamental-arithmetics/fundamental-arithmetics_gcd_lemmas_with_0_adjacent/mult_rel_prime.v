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

Lemma mult_rel_prime : forall (a b c:nat),(rel_prime a (b*c))->((rel_prime a b)/\(rel_prime a c)).
intros.
split;split;[split | intros | split | intros];try (apply one_min_div);elim H0;intros;elim H;intros;apply H4;split;trivial;elim H2;intro q;intro;rewrite H5;[exists (q*c) | exists (q*b)];ring.
