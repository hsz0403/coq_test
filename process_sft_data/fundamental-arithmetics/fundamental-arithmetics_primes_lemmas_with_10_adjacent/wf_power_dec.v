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
Admitted.

Lemma in_wf : forall (l:list (nat*nat))(p n:nat),(In (p,n) l)->(is_wf l)->(is_prime p)/\(n>0).
induction l;simpl;try tauto.
intros;destruct a.
inversion H0.
case (in_inv H);intros.
inversion H8;rewrite <- H10;rewrite <- H11;try tauto.
Admitted.

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
Admitted.

Lemma wf_impl_pwd : forall (l:list (nat*nat)),(is_wf l)->(is_pwd l).
induction l;intro.
apply nil_is_pwd.
destruct a.
inversion H.
apply cons_is_pwd;auto.
intros;intro.
assert (rel_prime n n).
eapply rel_prime_wf;[apply H7 | apply H].
generalize (gcd_refl n);intro.
unfold rel_prime in H8.
assert (1=n).
eapply gcd_unique;eauto.
Admitted.

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
Admitted.

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
Admitted.

Lemma pwd_impl_set : forall (l:list (nat*nat)),(is_pwd l)->(is_set (nat*nat) l).
Admitted.

Lemma factorisation_unique_upto_perm : forall (l l':list (nat*nat)),(is_wf l)->(is_wf l')->(refactor l)=(refactor l')->(is_permutation (nat*nat) l l').
intros.
assert (forall (x n:nat),(In (x,n) l)->(In (x,n) l')).
apply factorisation_unique_upto_equiv_aux;trivial.
assert (forall (x n:nat),(In (x,n) l')->(In (x,n) l)).
apply factorisation_unique_upto_equiv_aux;auto.
Admitted.

Theorem factorisation_exists : forall (n:nat),n<>0->{l:list (nat*nat) | (is_factorisation n l)}.
intros.
Admitted.

Theorem factorisation_unique_upto_permutation : forall (n:nat)(l l':list (nat*nat)),(is_factorisation n l)->(is_factorisation n l')->(is_permutation (nat*nat) l l').
unfold is_factorisation;intros.
elim H;intros.
elim H0;intros.
Admitted.

Lemma is_power_m_dec : forall (n m:nat),(m>0)->{x:nat | n=(power x m)}+{p:nat & {q:nat & {r:nat & {k:nat | (is_prime p)/\(0<r)/\(r<m)/\n=(power p (q*m+r))*k/\(rel_prime p k)}}}}.
intros n m;intro H.
case (eq_nat_dec n 0);intro.
left;exists 0.
destruct m;simpl;try omega;trivial.
generalize (factorisation_exists n n0);intro.
elim H0;intro l;intro.
elim p;intros.
Admitted.

Lemma wf_power_dec : forall (n:nat)(l:list (nat*nat)),(is_wf l)->(n>0)->{x:nat | (refactor l)=(power x n)}+{p:nat & {q:nat & {r:nat & {k:nat | (is_prime p)/\(0<r)/\(r<n)/\(refactor l)=(power p (q*n+r))*k/\(rel_prime p k)}}}}.
intro.
induction l;simpl;intros.
left;exists 1;rewrite power_one;trivial.
destruct a.
assert (n<>0);try omega.
generalize (quo_rem_euclide n1 n H1);intro.
case (eq_nat_dec (remainder_euclide n1 n H1) 0);intro.
rewrite e in H2;rewrite plus_comm in H2;simpl in H2.
case IHl;intros;trivial.
inversion H;trivial.
elim s;intro y;intro.
rewrite H2.
left;rewrite p;rewrite (mult_comm n);rewrite <- power_power_lemma1;rewrite <- power_mult_lemma1;exists (power n0 (quotient_euclide n1 n H1)*y);trivial.
elim s;intro p;intro.
elim p0;intro q;intro.
elim p1;intro r;intro.
elim p2;intro k;intro.
elim p3;intros.
elim H4;intros.
elim H6;intros.
elim H8;intros.
right.
exists p;exists q;exists r.
rewrite H9;rewrite mult_comm;rewrite <- mult_assoc.
exists (k*(power n0 n1)).
split;trivial.
split;trivial.
split;trivial.
split;trivial.
apply rel_prime_mult;trivial.
inversion H.
rewrite H9 in H17.
elim (mult_rel_prime n0 (power p (q*n+r)) k H17);intros.
apply rel_prime_power;apply rel_prime_sym;apply power_rel_prime with (q*n+r);trivial.
rewrite plus_comm;auto with arith.
right.
exists n0;exists (quotient_euclide n1 n H1);exists (remainder_euclide n1 n H1).
rewrite (mult_comm (quotient_euclide n1 n H1));rewrite <- H2.
exists (refactor l).
elim (in_wf ((n0,n1)::l) n0 n1);intros.
split;trivial.
split;trivial.
destruct (remainder_euclide n1 n H1);try tauto;auto with arith.
split;trivial.
apply rem_euclide.
split;trivial.
inversion H;trivial.
simpl;tauto.
trivial.
