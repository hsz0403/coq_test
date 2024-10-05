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

Theorem nth_root_irrational : forall (p k a b n q r:nat),(is_prime p)->(rel_prime p k)->(0<r)->(r<n)->(b<>0)->((power p (q*n+r))*k*(power b n) <> (power a n)).
intros.
intro.
rewrite power_plus_lemma1 in H4.
assert (divides a (power p q)).
apply prime_power_qn with n;try (auto with arith);try omega.
exists ((power p r)*k*(power b n)).
rewrite <- H4;ring.
assert (0<n);try omega.
elim H5;intro a';intro.
rewrite H7 in H4.
rewrite power_mult_lemma1 in H4;rewrite power_power_lemma1 in H4.
assert ((power p (q*n))<>0).
intro;apply not_prime_zero;generalize (power_zero (q*n) p H8);intro;rewrite H9 in H;trivial.
rewrite <- (mult_assoc (power p (q*n))) in H4;rewrite <- (mult_assoc (power p (q*n))) in H4.
generalize (mult_lemma6 (power p r*k*power b n) (power a' n) (power p (q*n)) H8 H4).
fold (power p r * k * power b n <> power a' n).
apply nth_root_irrat;trivial.
