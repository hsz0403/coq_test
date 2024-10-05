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
rewrite <- H10;trivial.
