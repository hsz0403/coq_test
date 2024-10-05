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

Lemma nat_factor_prime : forall (n:nat),(n<>0)->(n<>1)->{p:nat & {m:nat & {q:nat | (is_prime p)/\(m>0)/\(n=(power p m)*q)/\(is_gcd 1 p q)/\(q<n)}}}.
intros.
case (prime_dec n);intro.
exists n;exists 1;exists 1;simpl.
split;try tauto.
split;try omega.
split;try ring.
split;try omega.
apply gcd_sym;apply gcd_one.
elim (not_prime_impl_prime_divides n n0);intro;try tauto.
elim a;intro p;intro.
elim p0;intros.
elim (nat_factor n p H1).
intro m;intro.
elim p1;intros.
exists p;exists m;exists (quo n (power p m) H3).
split;trivial.
split.
destruct m;try omega.
elim H4;simpl;rewrite mult_comm;simpl;rewrite plus_comm;simpl;trivial.
split.
apply (quo_is_quo n (power p m) H3).
generalize (gcd_is_gcd p (quo n (power p m) H3));intro.
assert ((gcd p (quo n (power p m) H3))=1).
case (prime_gcd (gcd p (quo n (power p m) H3)) p (quo n (power p m) H3));trivial.
apply gcd_sym;trivial.
intro.
rewrite H6 in H5;elim H5;intros.
elim H7;intros.
elim H4;rewrite plus_comm;simpl.
generalize (quo_is_quo n (power p m) H3);intro.
elim H10;intros.
rewrite H12 in H11.
exists x;rewrite H11;ring.
rewrite H6 in H5;trivial.
generalize (quo_is_quo n (power p m) H3);intro.
split;trivial.
rewrite H7;rewrite mult_comm;apply mult_lemma3.
intro.
apply H;rewrite H7.
rewrite H8;ring.
red;apply power_lt.
destruct p.
elim (not_prime_zero H1).
destruct p;try omega.
elim H1;tauto.
destruct m;try omega.
elim H4;simpl;rewrite mult_comm;simpl;rewrite plus_comm;simpl;trivial.
trivial.
