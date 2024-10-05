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

Lemma prime_power_divides_refactor : forall (p n m:nat)(l:list (nat*nat)),(is_prime p)->(n>0)->(is_wf l)->(divides (refactor l) (power p n))->(In (p,m) l)->(n<=m).
induction l;simpl;intros;try tauto.
case H3;intro.
rewrite H4 in H2.
rewrite H4 in H1;inversion H1.
generalize (rel_prime_power p (refactor l) n (rel_prime_sym p (refactor l) H11));intro.
rewrite mult_comm in H2.
generalize (gauss (power p n) (refactor l) (power p m) H12 H2);intro.
apply power_divides_power with p;trivial.
destruct p.
elim (not_prime_zero H8).
elim H8;omega.
destruct a.
inversion H1.
apply IHl;trivial.
apply gauss with (power n0 n1);trivial.
apply rel_prime_power;apply rel_prime_sym;apply rel_prime_power.
apply (rel_prime_wf l p m n0 n1);trivial.
