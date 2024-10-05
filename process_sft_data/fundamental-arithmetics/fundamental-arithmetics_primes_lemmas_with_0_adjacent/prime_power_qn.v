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

Lemma prime_power_qn : forall (p n q x:nat),(is_prime p)->(divides (power x n) (power p (q*n)))->(1<=n)->(divides x (power p q)).
induction q;simpl;intros.
apply one_min_div.
rewrite power_plus_lemma1 in H0.
assert (divides x (power p q)).
apply IHq;trivial.
elim H0;intros;exists ((power p n)*x0).
rewrite H2;ring.
elim H2;intros.
rewrite H3 in H0.
rewrite power_mult_lemma1 in H0;rewrite power_power_lemma1 in H0;rewrite (mult_comm (power p n)) in H0.
elim H0;intros.
assert ((power p (q*n))<>0).
intro.
generalize (power_zero (q*n) p H5).
intro.
apply not_prime_zero.
rewrite H6 in H;trivial.
rewrite <- mult_assoc in H4.
generalize (mult_lemma6 (power x0 n) ((power p n)*x1) (power p (q*n)) H5 H4).
intro.
assert (exists n':nat,n=(S n')).
inversion H1;[exists 0 | exists m];trivial.
elim H7;intro n';intro.
rewrite H8 in H6;simpl in H6.
assert (divides x0 p).
case (prime_mult p x0 (power x0 n'));trivial.
rewrite H6.
exists ((power p n')*x1);ring.
intro.
apply prime_power with n';trivial.
elim H9;intros.
rewrite H10 in H3.
rewrite H3.
exists x2;ring.
