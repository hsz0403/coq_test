Require Import missing.
Require Import division.
Require Import euclide.
Require Import power.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition is_cd (d a b : nat) := (divides a d)/\(divides b d).
Definition is_gcd (d a b:nat) := (is_cd d a b)/\(forall (d':nat),(is_cd d' a b)->(divides d d')).
Definition f (x:nat*nat) := (fst x)+(snd x).
Definition R (x y:nat*nat) := (f x)<(f y).
Definition gcd (a b:nat) := let (d,_):=(gcd_exists a b) in d.
Definition rel_prime (a b:nat) := (is_gcd 1 a b).

Lemma bezout_aux1 : forall (x y u v:nat),(x<=y)->(is_gcd (u*x-v*(y-x)) x (y-x))->(is_gcd ((u+v)*x-v*y) x y).
intros.
elim (gcd_minus ((u+v)*x-v*y) x y H);intros.
apply H2.
Admitted.

Lemma bezout_aux2 : forall (x y u v:nat),(x<=y)->(is_gcd (v*(y-x)-u*x) x (y-x))->(is_gcd (v*y-(u+v)*x) x y).
intros.
elim (gcd_minus (v*y-(u+v)*x) x y H);intros.
apply H2.
Admitted.

Lemma bezout_exists_prod : forall (x:nat*nat),{y:nat*nat | (is_gcd ((fst y)*(fst x)-(snd y)*(snd x)) (fst x) (snd x))}+{y:nat*nat | (is_gcd ((snd y)*(snd x)-(fst y)*(fst x)) (fst x) (snd x))}.
apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => ({y:nat*nat | (is_gcd ((fst y)*(fst x)-(snd y)*(snd x)) (fst x) (snd x))}+{y:nat*nat | (is_gcd ((snd y)*(snd x)-(fst y)*(fst x)) (fst x) (snd x))})%type)).
unfold ltof.
unfold f.
intros.
case (lt_eq_lt_dec (fst x) (snd x));intro.
case s;intro.
destruct (fst x).
right;exists (0,1);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_zero.
elim (H (S n,snd x-S n));try (intro;simpl).
elim a;intro y;intro.
left;exists ((fst y)+(snd y),(snd y)).
simpl;apply bezout_aux1;try (auto with arith).
elim b;intro y;intro.
right;exists ((fst y)+(snd y),(snd y)).
simpl;apply bezout_aux2;try (auto with arith).
simpl;omega.
rewrite e;left;exists (1,0);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_refl.
destruct (snd x).
left;exists (1,0);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_sym;apply gcd_zero.
elim (H (S n,fst x-S n));try (intro;simpl).
elim a;intro y;intro.
right;exists ((snd y),(fst y)+(snd y));apply gcd_sym.
simpl;apply bezout_aux1;try (auto with arith).
elim b;intro y;intro.
left;exists ((snd y),(fst y)+(snd y));apply gcd_sym.
simpl;apply bezout_aux2;try (auto with arith).
Admitted.

Theorem bezout_exists : forall (a b:nat),{u:nat & {v:nat | (is_gcd (a*u-b*v) a b)}}+{u:nat & {v:nat | (is_gcd (b*v-a*u) a b)}}.
intros.
elim (bezout_exists_prod (a,b));intro.
elim a0;destruct x;simpl;intros.
left;exists n;exists n0;rewrite mult_comm;rewrite (mult_comm b);trivial.
elim b0;destruct x;simpl;intros.
Admitted.

Theorem bezout : forall (d a b:nat),(is_gcd d a b)->exists u:nat,exists v:nat,d=a*u-b*v \/ d=b*v-a*u.
intros.
elim (bezout_exists a b);intro.
elim a0;intro u;intro;elim p;intro v;intro;exists u;exists v;left;apply (gcd_unique d (a*u-b*v) a b);trivial.
Admitted.

Theorem bezout_rel_prime : forall (a b:nat),(rel_prime a b)<->(exists u:nat, exists v:nat, 1=a*u-b*v \/ 1 = b*v-a*u).
intros.
unfold rel_prime.
split;intro.
apply bezout;trivial.
elim H;intro u;intro H0.
elim H0;intro v;intro.
unfold is_gcd;unfold is_cd.
split.
split;apply one_min_div.
intros.
elim H2;intros.
elim H3;intro q;intro.
elim H4;intro q';intro.
rewrite H5 in H1;rewrite H6 in H1.
case H1;intro.
exists (q*u-q'*v);rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;trivial.
Admitted.

Lemma gcd_mult : forall (d a b:nat),(is_gcd d a b)->(forall (n:nat),(is_gcd (n*d) (n*a) (n*b))).
unfold is_gcd;unfold is_cd.
intros.
elim H;intros.
elim H0;intros.
split.
elim H2;intro q;intro.
elim H3;intro q';intro.
rewrite H4;rewrite mult_assoc.
rewrite H5;rewrite mult_assoc.
split;[exists q;trivial | exists q';trivial].
intros.
elim H4;intros.
elim (bezout d a b);try (unfold is_gcd;unfold is_cd;trivial).
intro u;intro.
elim H7;intro v;intro.
elim H5;intro q;intro.
elim H6;intro q';intro.
Admitted.

Theorem gauss : forall (d a b:nat),(rel_prime a d)->(divides (a*b) d)->(divides b d).
unfold rel_prime.
intros.
elim (bezout 1 a d H);intro u;intro.
elim H1;intro v;intro.
elim H0;intro q;intro.
Admitted.

Lemma gcd_euclide : forall (d a b:nat)(H:(b<>0)),(is_gcd d a b)<->(is_gcd d b (remainder_euclide a b H)).
intros.
generalize (quo_rem_euclide a b H);intro.
red;split;intro.
rewrite H0 in H1.
elim H1;intros.
unfold is_gcd;unfold is_cd.
elim H2;intros.
split.
split;try tauto.
elim H4;intro q;intro.
elim H5;intro q';intro.
replace (b*(quotient_euclide a b H)) with (d*q'*(quotient_euclide a b H)) in H6.
assert ((remainder_euclide a b H)=(d*q-d*q'*(quotient_euclide a b H))).
rewrite <- H6;rewrite minus_plus;trivial.
rewrite <- mult_assoc in H8;rewrite <- mult_minus_lemma2 in H8.
exists (q-q'*(quotient_euclide a b H));trivial.
rewrite <- H7;trivial.
intros.
elim H6;intros.
apply H3.
unfold is_cd;split;try tauto.
elim H7;intro q;intro.
elim H8;intro q';intro.
rewrite H10.
replace (b*(quotient_euclide a b H)) with (d'*q*(quotient_euclide a b H)).
rewrite <- mult_assoc;rewrite <- mult_plus_distr_l.
exists (q*(quotient_euclide a b H)+q');trivial.
rewrite <- H9;trivial.
unfold is_gcd;unfold is_cd.
unfold is_gcd in H1;unfold is_cd in H1.
elim H1;intros.
elim H2;intros.
rewrite H0.
split.
split;try tauto.
elim H4;intro q;intro.
elim H5;intro q';intro.
rewrite H7.
replace (b*(quotient_euclide a b H)) with (d*q*(quotient_euclide a b H)).
rewrite <- mult_assoc;rewrite <- mult_plus_distr_l.
exists (q*(quotient_euclide a b H)+q');trivial.
rewrite <- H6;trivial.
intros.
apply H3.
split;try tauto.
elim H6;intros.
elim H7;intro q;intro.
elim H8;intro q';intro.
assert ((remainder_euclide a b H)=b*(quotient_euclide a b H)+(remainder_euclide a b H)-b*(quotient_euclide a b H)).
rewrite minus_plus;trivial.
rewrite H9 in H11.
exists (q-q'*(quotient_euclide a b H)).
rewrite mult_minus_lemma2;rewrite mult_assoc.
Admitted.

Lemma gcd_exists_prod_bis : forall (x:nat*nat),{d:nat | (is_gcd d (fst x) (snd x))}.
apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => {d:nat | (is_gcd d (fst x) (snd x))})).
unfold ltof;unfold f;intros.
case (lt_eq_lt_dec (fst x) (snd x));intro.
case s;intro.
case (eq_nat_dec (fst x) 0);intro.
rewrite e;exists (snd x);apply gcd_zero.
elim (H ((fst x),(remainder_euclide (snd x) (fst x) n)));simpl.
intro d;intro.
exists d.
apply gcd_sym.
elim (gcd_euclide d (snd x) (fst x) n);auto.
generalize (rem_euclide (snd x) (fst x) n);try omega.
rewrite e;exists (snd x);apply gcd_refl.
case (eq_nat_dec (snd x) 0);intro.
rewrite e;exists (fst x);apply gcd_sym;apply gcd_zero.
elim (H ((snd x),(remainder_euclide (fst x) (snd x) n)));simpl.
intro d;intro.
exists d.
elim (gcd_euclide d (fst x) (snd x) n);auto.
Admitted.

Lemma rel_prime_dec : forall (a b:nat),{rel_prime a b}+{~(rel_prime a b)}.
intros.
unfold rel_prime.
generalize (gcd_is_gcd a b);intro.
case (eq_nat_dec (gcd a b) 1);intro.
left;rewrite e in H;trivial.
Admitted.

Lemma rel_prime_mult : forall (a b c:nat),(rel_prime a b)->(rel_prime a c)->(rel_prime a (b*c)).
intros.
split.
split;try (apply one_min_div).
intros.
elim H1;intros.
case (rel_prime_dec b d');intro.
assert (divides c d').
apply gauss with b;trivial.
elim H0;intros.
apply H6;unfold is_cd;tauto.
generalize (gcd_is_gcd b d');intro.
assert ((gcd b d')<>1).
intro;apply n.
unfold rel_prime;rewrite <- H5;trivial.
generalize (gcd_div_l (gcd b d') b d' H4);intro.
generalize (gcd_div_r (gcd b d') b d' H4);intro.
assert (divides a (gcd b d')).
apply divides_trans with d';[apply H2 | apply H7].
elim H5.
apply divides_antisym.
apply one_min_div.
Admitted.

Lemma mult_rel_prime : forall (a b c:nat),(rel_prime a (b*c))->((rel_prime a b)/\(rel_prime a c)).
intros.
Admitted.

Lemma rel_prime_power : forall (d a n:nat),(rel_prime a d)->(rel_prime a (power d n)).
induction n;simpl;intros.
unfold rel_prime;apply gcd_sym;apply gcd_one.
generalize (IHn H);intro.
Admitted.

Lemma power_rel_prime : forall (d a n:nat),(n>0)->(rel_prime a (power d n))->(rel_prime a d).
destruct n;simpl;intros.
inversion H.
Admitted.

Lemma power_power_rel_prime : forall (a n b m:nat),(n>0)->(m>0)->((rel_prime (power a n) (power b m))<->(rel_prime a b)).
split;intro.
apply power_rel_prime with m;trivial;apply rel_prime_sym;apply power_rel_prime with n;trivial;apply rel_prime_sym;trivial.
Admitted.

Theorem gcd_exists_bis : forall (a b:nat),{d:nat | (is_gcd d a b)}.
intros.
elim (gcd_exists_prod_bis (a,b));intro d;simpl;intros.
exists d;trivial.
