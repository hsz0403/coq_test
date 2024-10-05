Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Hierarchy Seq_fct RInt PSeries.
Section Continuity.
Context {V : NormedModule R_AbsRing}.
End Continuity.
Section Derive.
Context {V : NormedModule R_AbsRing}.
End Derive.
Section Derive'.
Context {V : CompleteNormedModule R_AbsRing}.
End Derive'.
Section Comp.
Context {V : CompleteNormedModule R_AbsRing}.
End Comp.
Section RInt_comp.
Context {V : NormedModule R_AbsRing}.
End RInt_comp.
Definition PS_Int (a : nat -> R) (n : nat) : R := match n with | O => 0 | S n => a n / INR (S n) end.
Section ByParts.
Context {V : CompleteNormedModule R_AbsRing}.
End ByParts.

Lemma is_RInt_scal_derive : forall (f : R -> R) (g : R -> V) (f' : R -> R) (g' : R -> V) (a b : R), (forall t, Rmin a b <= t <= Rmax a b -> is_derive f t (f' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> is_derive g t (g' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous f' t) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous g' t) -> is_RInt (fun t => plus (scal (f' t) (g t)) (scal (f t) (g' t))) a b (minus (scal (f b) (g b)) (scal (f a) (g a))).
Proof.
intros f g f' g' a b Df Dg Cf' Cg' If'g.
apply (is_RInt_derive (fun t => scal (f t) (g t))).
intros t Ht.
refine (_ (filterdiff_scal_fct t f g _ _ _ (Df _ Ht) (Dg _ Ht))).
intros H.
apply: filterdiff_ext_lin H _ => u.
by rewrite scal_distr_l !scal_assoc /mult /= Rmult_comm.
exact Rmult_comm.
intros t Ht.
apply: continuous_plus.
apply: continuous_scal.
now apply Cf'.
apply ex_derive_continuous.
eexists.
now apply Dg.
apply: continuous_scal.
apply: ex_derive_continuous.
eexists.
now apply Df.
now apply Cg'.
