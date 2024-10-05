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

Theorem nth_root_irrat : forall (p k a b n r:nat),(is_prime p)->(rel_prime p k)->(0<r)->(r<n)->(b<>0)->((power p r)*k*(power b n) <> (power a n)).
intros.
intro.
generalize (gcd_is_gcd a b);intro.
generalize (quo_is_quo a (gcd a b) (gcd_div_l (gcd a b) a b H5));intro.
generalize (quo_is_quo b (gcd a b) (gcd_div_r (gcd a b) a b H5));intro.
assert ((power a n)=(power (gcd a b * quo a (gcd a b) (gcd_div_l (gcd a b) a b H5)) n));try (rewrite <- H6;trivial).
assert ((power b n)=(power (gcd a b * quo b (gcd a b) (gcd_div_r (gcd a b) a b H5)) n));try (rewrite <- H7;trivial).
rewrite power_mult_lemma1 in H8;rewrite H8 in H4.
rewrite power_mult_lemma1 in H9;rewrite H9 in H4.
rewrite mult_lemma7 in H4.
assert ((power (gcd a b) n)<>O).
intro.
generalize (power_zero n (gcd a b) H10);intro.
apply (gcd_non_zero (gcd a b) a b);trivial.
generalize (mult_lemma6 (power p r * k * power (quo b (gcd a b) (gcd_div_r (gcd a b) a b H5)) n) (power (quo a (gcd a b) (gcd_div_l (gcd a b) a b H5)) n) (power (gcd a b) n) H10 H4).
fold ((power p r * k * power (quo b (gcd a b) (gcd_div_r (gcd a b) a b H5)) n)<>(power (quo a (gcd a b) (gcd_div_l (gcd a b) a b H5)) n)).
apply nth_root_irrat_aux;trivial.
apply gcd_rel_prime;apply (gcd_non_zero (gcd a b) a b);trivial.
