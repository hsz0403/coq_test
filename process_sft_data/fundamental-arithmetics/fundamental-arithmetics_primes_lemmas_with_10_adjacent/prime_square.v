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

Lemma not_prime_zero : ~(is_prime O).
unfold is_prime.
intro.
elim H;intros.
Admitted.

Lemma is_prime_2 : (is_prime 2).
unfold is_prime.
split.
intro;discriminate.
intros.
elim H;destruct x;rewrite mult_comm.
intro;discriminate.
simpl.
case d.
simpl.
rewrite mult_comm;simpl;intro;discriminate.
intros.
inversion H0.
symmetry in H2.
case (plus_is_one n (x*(S n)) H2);intro.
elim a;intros.
left;rewrite H1;trivial.
elim a;intros.
Admitted.

Lemma prime_div_gcd : forall (p a:nat),(is_prime p)->~(divides a p)->(rel_prime p a).
unfold is_prime.
unfold rel_prime.
intros.
unfold is_gcd;unfold is_cd.
split.
split;apply one_min_div.
intros.
elim H;intros.
elim H1;intros.
case (H3 d' H4);intro.
rewrite H6;apply divides_refl.
Admitted.

Lemma prime_gcd : forall (d p a:nat),(is_prime p)->(is_gcd d a p)->(d=1)\/(d=p).
unfold is_prime.
intros.
elim H;intros.
apply H2.
elim H0;intros.
Admitted.

Lemma prime_rel_prime : forall (p a:nat),(is_prime p)->~(rel_prime a p)->(divides a p).
unfold rel_prime.
intros.
generalize (gcd_is_gcd a p);intros.
case (prime_gcd (gcd a p) p a H H1);intro;rewrite H2 in H1;try tauto.
elim H1;intros.
Admitted.

Lemma prime_mult : forall (p a b:nat),(is_prime p)->(divides (a*b) p)->((divides a p)\/(divides b p)).
intros.
generalize (gcd_is_gcd a p);intro.
case (prime_gcd (gcd a p) p a H H1);intro;rewrite H2 in H1.
right;apply gauss with a;trivial.
red in H1;elim H1;intros.
Admitted.

Lemma prime_power : forall (p n x:nat),(is_prime p)->(divides (power x n) p)->(divides x p).
induction n;simpl;intros.
elim H;intros.
elim H1;apply divides_antisym;trivial;apply one_min_div.
case (prime_mult p x (power x n) H H0);trivial.
Admitted.

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
Admitted.

Lemma divides_prime : forall (a:nat),(exists p:nat,(p<>a)/\(is_prime p)/\(divides a p)) -> ~(is_prime a).
intros;intro.
elim H;intro p;intro.
elim H1;intros.
elim H3;intros.
unfold is_prime in H0.
elim H0;intros.
unfold is_prime in H4.
elim H4;intros.
Admitted.

Lemma gcd_prime : forall (p:nat),(p<>1)->(forall (d a:nat),(is_gcd d a p)->(d=1)\/(d=p))->(is_prime p).
intros.
split;try tauto.
intro d';intro.
assert (is_gcd d' d' p).
unfold is_gcd;unfold is_cd.
split;[split;[apply divides_refl | tauto] | tauto].
Admitted.

Lemma prime_cond : forall (p:nat),((p<>1)/\(forall (a:nat),(a<>1)->(a<>p)->~(divides p a))<->(is_prime p)).
split;intros.
elim H;intros.
split;try tauto.
intros.
case (eq_nat_dec d 1);intro;try tauto.
case (eq_nat_dec d p);intro;try tauto.
elim (H1 d n n0 H2).
elim H;intros.
split;try tauto.
intros;intro.
Admitted.

Lemma prime_dec : forall (n:nat),{is_prime n}+{~(is_prime n)}.
intro.
case (divides_nat n);intro.
elim s;intros.
right;intro.
unfold is_prime in H.
elim H;intros.
elim (H1 x);try tauto.
case (eq_nat_dec n 1);intro.
right;unfold is_prime;tauto.
left;unfold is_prime.
split;trivial.
intros.
case (eq_nat_dec d 1);try tauto.
case (eq_nat_dec d n);try tauto;intros.
Admitted.

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

Lemma prime_square : forall (p a:nat),(is_prime p)->(divides (square a) p)->(divides a p).
unfold square.
intros;case (prime_mult p a a H H0);trivial.
