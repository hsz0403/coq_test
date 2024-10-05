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

Lemma bezout_aux2 : forall (x y u v:nat),(x<=y)->(is_gcd (v*(y-x)-u*x) x (y-x))->(is_gcd (v*y-(u+v)*x) x y).
intros.
elim (gcd_minus (v*y-(u+v)*x) x y H);intros.
apply H2.
rewrite mult_plus_distr_r;rewrite plus_comm;rewrite <- minus_minus_lemma2;rewrite <- mult_minus_lemma2;trivial.
