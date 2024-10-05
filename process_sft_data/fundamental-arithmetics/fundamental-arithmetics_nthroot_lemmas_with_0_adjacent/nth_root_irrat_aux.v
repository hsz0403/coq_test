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

Lemma nth_root_irrat_aux : forall (p k a b n r:nat),(is_prime p)->(rel_prime p k)->(0<r)->(r<n)->(rel_prime a b)->((power p r)*k*(power b n) <> (power a n)).
intros.
intro.
assert (divides a p).
apply prime_power with n;trivial.
generalize (power_divides_lemma1 r p H1);intro.
elim H5;intro q;intros.
rewrite H6 in H4.
rewrite <- H4;exists (q*k*(power b n));ring.
assert (divides b p).
elim H5;intro q;intros.
rewrite H6 in H4.
rewrite power_mult_lemma1 in H4.
assert ((power p n)=(power p (r+(n-r)))).
rewrite <- le_plus_minus;try (auto with arith).
rewrite H7 in H4;rewrite power_plus_lemma1 in H4.
assert ((power p r)<>O).
intro.
apply not_prime_zero.
assert (p=O).
apply power_zero with r;trivial.
rewrite H9 in H;trivial.
rewrite <- mult_assoc in H4;rewrite <- mult_assoc in H4;generalize (mult_lemma6 (k*(power b n)) ((power p (n-r))*(power q n)) (power p r) H8 H4);intro.
assert (divides (power p (n-r)) p).
apply power_divides_lemma1;apply minus_lt_lemma1;trivial.
apply prime_power with n;trivial.
apply gauss with k;try (apply rel_prime_sym;trivial).
rewrite H9;apply divides_mult;trivial.
elim H3;intros.
elim H;intros.
apply H9;apply divides_antisym;try (apply one_min_div).
apply H8;red;tauto.
