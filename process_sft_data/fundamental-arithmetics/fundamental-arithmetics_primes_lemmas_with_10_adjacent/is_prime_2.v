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

Lemma prime_square : forall (p a:nat),(is_prime p)->(divides (square a) p)->(divides a p).
unfold square.
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
right;rewrite H1;trivial.
