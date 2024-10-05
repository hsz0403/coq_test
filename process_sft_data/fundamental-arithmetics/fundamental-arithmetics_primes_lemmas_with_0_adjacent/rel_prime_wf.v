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

Lemma rel_prime_wf : forall (l:list (nat*nat))(p n q m:nat),(In (p,n) l)->(is_wf ((q,m)::l))->(rel_prime p q).
induction l;simpl;intros;try tauto.
destruct a.
inversion H0;case (in_inv H);intro.
rewrite H8 in H7;simpl in H7.
elim (in_wf ((n0,n1)::l) p n H);trivial;intros.
elim (mult_rel_prime q (power p n) (refactor l) H7);intros.
apply rel_prime_sym;apply power_rel_prime with n;trivial.
apply (IHl p n q m);trivial.
apply cons_is_wf;trivial.
inversion H6;trivial.
simpl in H7;elim (mult_rel_prime q (power n0 n1) (refactor l) H7);auto.
