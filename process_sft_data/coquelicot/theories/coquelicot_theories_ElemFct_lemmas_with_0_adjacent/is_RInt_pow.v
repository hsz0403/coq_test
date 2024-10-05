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

Lemma is_RInt_pow : forall a b n, is_RInt (fun x => pow x n) a b (pow b (S n) / INR (S n) - pow a (S n) / INR (S n)).
Proof.
intros a b n.
set f := fun x => pow x (S n) / INR (S n).
fold (f a) (f b).
assert (H: forall x : R, is_derive f x (pow x n)).
intros x.
evar_last.
rewrite /f /Rdiv -[Rmult]/(scal (V := R_NormedModule)).
apply is_derive_scal_l.
apply is_derive_pow, is_derive_id.
rewrite /pred.
set k := INR (S n).
rewrite /scal /= /mult /one /=.
field.
rewrite /k S_INR.
apply Rgt_not_eq, INRp1_pos.
apply: is_RInt_derive => x Hx //.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
apply derivable_pt_pow.
