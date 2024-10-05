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

Lemma sqrt_prime_irrat_aux : forall (p k a b:nat),(is_prime p)->(rel_prime p k)->(rel_prime a b)->(p*k*(square b) <> (square a)).
intros.
intro.
assert (divides a p).
apply prime_square;trivial.
exists (k*(square b)).
rewrite <- H2;ring.
elim H3;intro n_a;intro.
rewrite H4 in H2;rewrite square_mult_lemma in H2;unfold square in H2.
assert (k*(b*b)=p*(n_a*n_a)).
apply mult_lemma6 with p.
intro H5;rewrite H5 in H;apply not_prime_zero;trivial.
rewrite mult_assoc;rewrite H2;ring.
assert (divides b p).
apply prime_square;trivial;unfold square.
apply gauss with k.
apply rel_prime_sym;trivial.
exists (n_a*n_a);trivial.
assert (p=1).
unfold rel_prime in H1.
elim H1;intros.
apply divides_antisym;try (apply one_min_div).
apply H8;red;tauto.
elim H;tauto.
