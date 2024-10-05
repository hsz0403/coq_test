Require Import missing.
Require Import division.
Require Import euclide.
Require Import gcd.
Require Import power.
Require Import permutation.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition is_prime (p:nat) := (p<>1)/\(forall (d:nat),(divides p d)->(d=1)\/(d=p)).
Fixpoint refactor (l:(list (nat*nat))) {struct l} : nat := match l with nil => 1 | (cons (p,n) tail) => (power p n)*(refactor tail) end.
Inductive is_wf : (list (nat*nat))->Prop := nil_is_wf : (is_wf nil) |cons_is_wf : forall (p n:nat)(tail:(list (nat*nat))),(is_prime p)->(n>0)->(is_wf tail)->(rel_prime p (refactor tail))->(is_wf (cons (p,n) tail)).
Inductive is_pwd : list (nat*nat) -> Prop := nil_is_pwd : (is_pwd nil) |cons_is_pwd : forall (p n:nat)(tail:list (nat*nat)),(is_pwd tail)->(forall (n:nat),~(In (p,n) tail))->(is_pwd ((p,n)::tail)).
Definition is_factorisation (n:nat)(l:list (nat*nat)) := (is_wf l)/\(n=(refactor l)).

Lemma prime_divides_refactor : forall (p:nat)(l:list (nat*nat)),(is_prime p)->(is_wf l)->(divides (refactor l) p)->(exists m:nat,(In (p,m) l)).
induction l;simpl;intros.
assert (p=1).
apply divides_antisym;trivial.
apply one_min_div.
rewrite H2 in H;elim H;tauto.
destruct a.
case (divides_dec (power n n0) p);intro.
generalize (prime_power p n0 n H d);intro.
assert (n=p).
inversion H0.
elim H6.
intros.
elim H;intros.
case (H11 p H2);try tauto;try omega.
exists n0;rewrite <- H3;left;trivial.
inversion H0.
elim (IHl H H7).
intros;exists x;tauto.
apply gauss with (power n n0);trivial.
apply rel_prime_sym;apply prime_div_gcd;trivial.
