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

Theorem bezout_exists : forall (a b:nat),{u:nat & {v:nat | (is_gcd (a*u-b*v) a b)}}+{u:nat & {v:nat | (is_gcd (b*v-a*u) a b)}}.
intros.
elim (bezout_exists_prod (a,b));intro.
elim a0;destruct x;simpl;intros.
left;exists n;exists n0;rewrite mult_comm;rewrite (mult_comm b);trivial.
elim b0;destruct x;simpl;intros.
right;exists n;exists n0;rewrite mult_comm;rewrite (mult_comm a);trivial.
