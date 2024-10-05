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

Lemma gcd_exists_prod : forall (x:nat*nat),{d:nat | (is_gcd d (fst x) (snd x))}.
apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => {d:nat | (is_gcd d (fst x) (snd x))})).
unfold ltof.
unfold f.
intros.
case (lt_eq_lt_dec (fst x) (snd x));intro.
case s;intro.
destruct (fst x).
exists (snd x);apply gcd_zero.
elim (H (S n,snd x-S n)).
simpl;intro d;intro.
exists d.
elim (gcd_minus d (S n) (snd x));try (auto with arith).
simpl.
omega.
rewrite e;exists (snd x);apply gcd_refl.
destruct (snd x).
exists (fst x);apply gcd_sym;apply gcd_zero.
elim (H (S n,fst x-S n)).
simpl;intro d;intro.
exists d.
apply gcd_sym.
elim (gcd_minus d (S n) (fst x));try (auto with arith).
simpl.
omega.
