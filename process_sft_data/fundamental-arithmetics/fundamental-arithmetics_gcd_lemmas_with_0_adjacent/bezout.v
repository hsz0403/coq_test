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

Theorem bezout : forall (d a b:nat),(is_gcd d a b)->exists u:nat,exists v:nat,d=a*u-b*v \/ d=b*v-a*u.
intros.
elim (bezout_exists a b);intro.
elim a0;intro u;intro;elim p;intro v;intro;exists u;exists v;left;apply (gcd_unique d (a*u-b*v) a b);trivial.
elim b0;intro u;intro;elim p;intro v;intro;exists u;exists v;right;apply (gcd_unique d (b*v-a*u) a b);trivial.
