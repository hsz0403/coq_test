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

Lemma is_RInt_scal_derive_r : forall (f : R -> R) (g : R -> V) (f' : R -> R) (g' : R -> V) (a b : R) (l : V), (forall t, Rmin a b <= t <= Rmax a b -> is_derive f t (f' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> is_derive g t (g' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous f' t) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous g' t) -> is_RInt (fun t => scal (f' t) (g t)) a b l -> is_RInt (fun t => scal (f t) (g' t)) a b (minus (minus (scal (f b) (g b)) (scal (f a) (g a))) l).
Proof.
intros f g f' g' a b l Df Dg Cf' Cg' If'g.
apply (is_RInt_ext (fun t => minus (plus (scal (f' t) (g t)) (scal (f t) (g' t))) (scal (f' t) (g t)))).
intros x H.
by rewrite /minus (plus_comm (scal (f' x) _)) -plus_assoc plus_opp_r plus_zero_r.
apply is_RInt_minus with (2 := If'g).
exact: is_RInt_scal_derive.
