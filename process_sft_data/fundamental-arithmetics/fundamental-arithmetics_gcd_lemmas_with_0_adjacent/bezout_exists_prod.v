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

Lemma bezout_exists_prod : forall (x:nat*nat),{y:nat*nat | (is_gcd ((fst y)*(fst x)-(snd y)*(snd x)) (fst x) (snd x))}+{y:nat*nat | (is_gcd ((snd y)*(snd x)-(fst y)*(fst x)) (fst x) (snd x))}.
apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => ({y:nat*nat | (is_gcd ((fst y)*(fst x)-(snd y)*(snd x)) (fst x) (snd x))}+{y:nat*nat | (is_gcd ((snd y)*(snd x)-(fst y)*(fst x)) (fst x) (snd x))})%type)).
unfold ltof.
unfold f.
intros.
case (lt_eq_lt_dec (fst x) (snd x));intro.
case s;intro.
destruct (fst x).
right;exists (0,1);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_zero.
elim (H (S n,snd x-S n));try (intro;simpl).
elim a;intro y;intro.
left;exists ((fst y)+(snd y),(snd y)).
simpl;apply bezout_aux1;try (auto with arith).
elim b;intro y;intro.
right;exists ((fst y)+(snd y),(snd y)).
simpl;apply bezout_aux2;try (auto with arith).
simpl;omega.
rewrite e;left;exists (1,0);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_refl.
destruct (snd x).
left;exists (1,0);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_sym;apply gcd_zero.
elim (H (S n,fst x-S n));try (intro;simpl).
elim a;intro y;intro.
right;exists ((snd y),(fst y)+(snd y));apply gcd_sym.
simpl;apply bezout_aux1;try (auto with arith).
elim b;intro y;intro.
left;exists ((snd y),(fst y)+(snd y));apply gcd_sym.
simpl;apply bezout_aux2;try (auto with arith).
simpl;omega.
