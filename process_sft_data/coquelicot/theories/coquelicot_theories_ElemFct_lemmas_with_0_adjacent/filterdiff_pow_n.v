Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.
Section nat_to_ring.
Context {K : Ring}.
Definition nat_to_ring (n : nat) : K := sum_n_m (fun _ => one) 1 n.
End nat_to_ring.
Section is_derive_mult.
Context {K : AbsRing}.
End is_derive_mult.

Lemma filterdiff_pow_n {K : AbsRing} (x : K) (n : nat) : (forall a b : K, mult a b = mult b a) -> filterdiff (fun y : K => pow_n y n) (locally x) (fun y : K => scal y (mult (nat_to_ring n) (pow_n x (pred n)))).
Proof.
intros Hmult.
rewrite -/(is_derive (fun y : K => pow_n y n) x (mult (nat_to_ring n) (pow_n x (pred n)))).
elim: n => [ | n IH] /=.
evar_last.
apply is_derive_const.
by rewrite nat_to_ring_O mult_zero_l.
evar_last.
eapply is_derive_mult.
apply is_derive_id.
apply IH.
by apply Hmult.
simpl.
rewrite nat_to_ring_Sn mult_one_l mult_assoc (Hmult x) -mult_assoc.
rewrite mult_distr_r mult_one_l plus_comm.
apply f_equal2 => //.
clear ; case: n => [ | n] //=.
by rewrite nat_to_ring_O !mult_zero_l.
