Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Hierarchy.
Definition is_domin {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T -> Prop) -> Prop) (f : T -> U) (g : T -> V) := forall eps : posreal, F (fun x => norm (g x) <= eps * norm (f x)).
Definition is_equiv {T} {K : AbsRing} {V : NormedModule K} (F : (T -> Prop) -> Prop) (f g : T -> V) := is_domin F g (fun x => minus (g x) (f x)).
Section Equiv.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv.
Section Domin.
Context {T : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv}.
End Domin.
Section Equiv_VS.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv_VS.
Section Domin_comp.
Context {T1 T2 : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T1 -> Prop) -> Prop) {FF : Filter F} (G : (T2 -> Prop) -> Prop) {FG : Filter G}.
End Domin_comp.

Lemma equiv_scal : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> V) (c : K), (exists y : K, mult y c = one) -> is_equiv F f g -> is_equiv F (fun x => scal c (f x)) (fun x => scal c (g x)).
Proof.
intros F FF f g c [y Hc] H.
apply domin_scal_l.
by exists y.
move => eps /=.
cut (F (fun x => norm (scal c (minus (g x) (f x))) <= eps * norm (g x))).
apply filter_imp => x.
now rewrite scal_distr_l scal_opp_r.
now apply domin_scal_r.
