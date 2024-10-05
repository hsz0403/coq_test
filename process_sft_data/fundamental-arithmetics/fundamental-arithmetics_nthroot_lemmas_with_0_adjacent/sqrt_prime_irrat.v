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

Theorem sqrt_prime_irrat : forall (p k a b:nat),(is_prime p)->(rel_prime p k)->(b<>O)->(p*k*(square b) <> (square a)).
intros.
generalize (gcd_is_gcd a b);intro.
generalize (quo_is_quo a (gcd a b) (gcd_div_l (gcd a b) a b H2));intro.
generalize (quo_is_quo b (gcd a b) (gcd_div_r (gcd a b) a b H2));intro.
intro.
rewrite H3 in H5.
replace (square b) with (square (gcd a b * quo b (gcd a b) (gcd_div_r (gcd a b) a b H2))) in H5;auto.
rewrite square_mult_lemma in H5;rewrite square_mult_lemma in H5.
assert (p*k*(square (quo b (gcd a b) (gcd_div_r (gcd a b) a b H2)))=(square (quo a (gcd a b) (gcd_div_l (gcd a b) a b H2)))).
apply mult_lemma6 with (square (gcd a b)).
unfold square.
generalize (gcd_non_zero (gcd a b) a b H1 H2);intro.
intro;apply H6.
case (mult_lemma2 (gcd a b) (gcd a b) H7);trivial.
rewrite <- H5;ring.
apply (sqrt_prime_irrat_aux p k (quo a (gcd a b) (gcd_div_l (gcd a b) a b H2)) (quo b (gcd a b) (gcd_div_r (gcd a b) a b H2)));auto.
apply gcd_rel_prime;apply (gcd_non_zero (gcd a b) a b);trivial.
