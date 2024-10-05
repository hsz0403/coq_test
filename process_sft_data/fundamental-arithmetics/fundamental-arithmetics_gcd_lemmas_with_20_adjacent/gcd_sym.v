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

Theorem gcd_unique : forall (d d' a b:nat),(is_gcd d a b)->(is_gcd d' a b)->d=d'.
unfold is_gcd.
intros.
elim H;elim H0;intros.
Admitted.

Lemma gcd_zero : forall (a:nat),(is_gcd a O a).
unfold is_gcd.
intro.
split.
red;split;[apply zero_max_div | apply divides_refl].
Admitted.

Lemma gcd_one : forall (a:nat),(is_gcd 1 1 a).
unfold is_gcd.
intros.
split.
red;split;[apply divides_refl | apply one_min_div].
Admitted.

Lemma gcd_minus : forall (d a b:nat),(a <= b)->((is_gcd d a b)<->(is_gcd d a (b-a))).
intros.
unfold is_gcd.
split;intro.
elim H0;intros.
split.
red in H1;red.
elim H1;intros.
split;try tauto.
apply divides_minus;trivial.
unfold is_cd;intros.
apply H2;red;elim H3;intros.
split;[tauto | rewrite (le_plus_minus a b H);apply divides_plus;trivial].
elim H0;unfold is_cd;intros.
split.
split;[tauto | elim H1;intros;rewrite (le_plus_minus a b H);apply divides_plus;trivial].
intros.
elim H3;intros;apply H2.
Admitted.

Lemma gcd_refl : forall (a:nat),(is_gcd a a a).
unfold is_gcd.
intros.
unfold is_cd.
split;try tauto.
Admitted.

Lemma gcd_div_l : forall (d a b:nat),(is_gcd d a b)->(divides a d).
Admitted.

Lemma gcd_div_r : forall (d a b:nat),(is_gcd d a b)->(divides b d).
Admitted.

Lemma Rwf : well_founded R.
unfold R.
Admitted.

Lemma gcd_exists_prod : forall (x:nat*nat),{d:nat | (is_gcd d (fst x) (snd x))}.
apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => {d:nat | (is_gcd d (fst x) (snd x))})).
unfold ltof.
unfold f.
intros.
case (lt_eq_lt_dec (fst x) (snd x));intro.
case s;intro.
destruct (fst x).
exists (snd x);apply gcd_zero.
elim (H (S n,snd x-S n)).
simpl;intro d;intro.
exists d.
elim (gcd_minus d (S n) (snd x));try (auto with arith).
simpl.
omega.
rewrite e;exists (snd x);apply gcd_refl.
destruct (snd x).
exists (fst x);apply gcd_sym;apply gcd_zero.
elim (H (S n,fst x-S n)).
simpl;intro d;intro.
exists d.
apply gcd_sym.
elim (gcd_minus d (S n) (fst x));try (auto with arith).
simpl.
Admitted.

Theorem gcd_exists : forall (a b:nat),{d:nat | (is_gcd d a b)}.
intros.
elim (gcd_exists_prod (a,b)).
Admitted.

Lemma gcd_is_gcd : forall (a b:nat),(is_gcd (gcd a b) a b).
intros.
unfold gcd.
generalize (gcd_exists a b).
Admitted.

Lemma rel_prime_sym : forall (a b:nat),(rel_prime a b)->(rel_prime b a).
unfold rel_prime.
Admitted.

Lemma rel_prime_1 : forall (a:nat),(rel_prime a 1).
unfold rel_prime.
Admitted.

Lemma gcd_rel_prime : forall (d a b:nat)(H:(is_gcd d a b)),(d <> O)->(rel_prime (quo a d (gcd_div_l d a b H)) (quo b d (gcd_div_r d a b H))).
unfold rel_prime.
intros.
generalize (quo_is_quo a d (gcd_div_l d a b H));intro.
generalize (quo_is_quo b d (gcd_div_r d a b H));intro.
unfold is_gcd;split;unfold is_cd.
split;apply one_min_div.
intros.
elim H3;intros.
elim H4;intro q;intro.
elim H5;intro q';intro.
rewrite H6 in H1.
rewrite H7 in H2.
assert (divides d (d*d')).
red in H;elim H;intros.
apply H9;red;split;[exists q;rewrite H1;ring | exists q';rewrite H2;ring].
elim H8;intros.
exists x.
apply mult_lemma6 with d;trivial.
Admitted.

Lemma gcd_non_zero : forall (d p q:nat),(q<>O)->(is_gcd d p q)->(d<>O).
unfold is_gcd.
intros.
elim H0;intros.
intro.
elim H1;intros.
elim H5;intros.
Admitted.

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

Lemma gcd_sym : forall (d a b:nat),(is_gcd d a b)->(is_gcd d b a).
unfold is_gcd.
intros.
elim H;intros.
split.
red;red in H0;tauto.
intros.
apply H1.
red;red in H2;tauto.
