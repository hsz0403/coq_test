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

Lemma factorisation_unique_upto_equiv_aux : forall (l l':list (nat*nat)),(is_wf l)->(is_wf l')->(refactor l)=(refactor l')->(forall (x n:nat),(In (x,n) l)->(In (x,n) l')).
intros l l';intro;intro;intro;intros p n;intro.
elim (in_wf l p n H2 H);intros.
generalize (factor_divides_refactor (p,n) l H2);simpl;intro.
rewrite H1 in H5.
assert (divides (refactor l') p).
apply divides_trans with (power p n);[trivial | apply power_divides_lemma1;auto with arith].
elim (prime_divides_refactor p l' H3 H0 H6);intro m;intro.
cut (n=m).
intro;rewrite H8;trivial.
apply le_antisym.
eapply prime_power_divides_refactor;eauto.
generalize (factor_divides_refactor (p,m) l' H7);simpl;intro.
rewrite <- H1 in H8.
apply prime_power_divides_refactor with p l;auto.
elim (in_wf l' p m);trivial.
