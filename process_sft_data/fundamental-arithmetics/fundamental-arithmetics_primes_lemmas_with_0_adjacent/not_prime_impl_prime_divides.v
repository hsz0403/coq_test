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

Lemma not_prime_impl_prime_divides : forall (n:nat),(~(is_prime n)->({p:nat | (is_prime p)/\(divides n p)}+{n=1})).
intro.
apply (lt_wf_rec n (fun n:nat => ~(is_prime n)->({p:nat | (is_prime p)/\(divides n p)}+{n=1})));intros.
case (eq_nat_dec n0 1);try tauto;intro.
case (eq_nat_dec n0 0);intro.
left;exists 2.
split;[apply is_prime_2 | rewrite e;apply zero_max_div].
case (divides_nat n0);intro.
elim s;intro d;intro.
elim p;intros.
elim H2;intros.
assert (d<n0).
generalize (divides_le n0 d n2 H4);omega.
case (prime_dec d);intro.
left;exists d;tauto.
elim (H d H5 n3);try tauto.
intro.
elim a;intro q;intro.
left;exists q.
split;try tauto.
apply divides_trans with d;try tauto.
elim (prime_cond n0);intros;elim H0;apply H1;auto.
