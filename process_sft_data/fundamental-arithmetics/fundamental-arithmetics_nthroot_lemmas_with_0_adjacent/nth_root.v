Require Import missing.
Require Import division.
Require Import gcd.
Require Import primes.
Require Import power.
Unset Standard Proposition Elimination Names.
Fact sqrt_prime : forall (p:nat),(is_prime p)->forall (a b:nat),(b<>O)->(p*(square b)<>(square a)).
intros.
replace p with (p*1);try (auto with arith).
apply sqrt_prime_irrat;trivial;apply rel_prime_1.
Fact sqrt_2_irrat : forall (p q:nat),(q<>O)->(2*(square q)<>(square p)).
intros.
apply sqrt_prime;trivial.
apply is_prime_2.

Theorem nth_root : forall (x n:nat),(n>0)->{y:nat | x=(power y n)}+{forall (a b:nat),(b<>0)->x*(power b n)<>(power a n)}.
intros.
case (is_power_m_dec x n H);intro;try tauto.
elim s;intro p;intro.
elim p0;intro q;intro.
elim p1;intro r;intro.
elim p2;intro k;intro.
right;intros.
assert (x=(power p (q*n+r))*k);try tauto.
rewrite H1;apply nth_root_irrational;tauto.
