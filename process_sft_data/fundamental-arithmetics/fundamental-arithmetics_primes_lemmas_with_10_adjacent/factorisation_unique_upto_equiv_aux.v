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
Admitted.

Lemma nat_factor : forall (n p:nat),(is_prime p)->(n<>0)->{m:nat | (divides n (power p m))/\~(divides n (power p (m+1)))}.
intros n p H.
apply (lt_wf_rec n (fun n:nat => n <> 0 -> {m : nat | divides n (power p m) /\ ~ divides n (power p (m + 1))}));intros.
case (divides_dec n0 p);intro.
generalize (quo_is_quo n0 p d);intro.
elim (H0 (quo n0 p d)).
intro m;intros.
exists (m+1).
elim p0;intros.
elim H3;intros.
rewrite H5 in H2;rewrite mult_assoc in H2.
rewrite plus_comm.
split;simpl.
exists x;trivial.
rewrite plus_comm;simpl.
rewrite (mult_comm p (power p m));rewrite mult_assoc;intro.
elim H6;intros.
rewrite H2 in H7.
assert (p<>0).
intro.
rewrite H8 in H.
apply not_prime_zero;trivial.
assert ((power p m)*x=(power p m)*p*x0).
apply mult_lemma6 with p;trivial.
rewrite mult_assoc;rewrite H7;ring.
rewrite <- H5 in H9;rewrite (mult_comm (power p m) p) in H9.
apply H4.
rewrite plus_comm;simpl.
exists x0;trivial.
rewrite mult_comm in H2;rewrite H2;apply mult_lemma3.
intro.
apply H1;rewrite H2;rewrite H3;trivial.
elim H.
intros.
destruct p;omega.
intro;apply H1.
rewrite H2;rewrite H3;ring.
exists 0;simpl.
split.
apply one_min_div.
Admitted.

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
Admitted.

Lemma factorisation : forall (n:nat),{l:(list (nat*nat)) | (is_wf l)/\n=(refactor l)}+{n=0}.
intro.
case (eq_nat_dec n 0);intro.
right;trivial.
case (eq_nat_dec n 1).
intro;left;exists (nil (A:=nat*nat)).
split;[apply nil_is_wf | simpl;trivial].
generalize n0.
apply (lt_wf_rec n (fun n:nat => n<>0 -> n <> 1 -> {l : list (nat * nat) | is_wf l /\ n = refactor l}+{n=0}));intros.
elim (nat_factor_prime n1 H0 H1).
intro p;intro.
elim p0;intro m;intro.
elim p1;intro q;intro.
elim p2;intros.
elim H3;intros.
elim H5;intros.
elim H7;intros.
case (eq_nat_dec q 1);intro.
left;exists (cons (p,m) nil);simpl;rewrite e in H6.
split;trivial.
apply cons_is_wf;auto;try (apply nil_is_wf).
unfold rel_prime;simpl;rewrite e in H8;trivial.
assert (q<>0).
intro;rewrite H10 in H6;rewrite mult_comm in H6;simpl in H6;auto.
elim (H q H9 H10 n2).
intro.
elim a;intro l;intro.
elim p3;intros.
left;exists (cons (p,m) l);simpl;rewrite H12 in H6;split;trivial.
apply cons_is_wf;auto.
rewrite <- H12;unfold rel_prime;trivial.
Admitted.

Lemma factor_divides_refactor : forall (x:nat*nat)(l:list (nat*nat)),(In x l)->(divides (refactor l) (power (fst x) (snd x))).
induction l;simpl;try tauto.
intro.
case H;intro.
destruct a.
rewrite <- H0;simpl.
exists (refactor l);trivial.
destruct a.
elim (IHl H0);intros.
rewrite H1.
Admitted.

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
