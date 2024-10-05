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

Lemma equiv_carac_1 : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g o : T -> V), (forall x, f x = plus (g x) (o x)) -> is_domin F g o -> is_equiv F f g.
Proof.
intros F FF f g o Ho Hgo.
intro eps ; move: (Hgo eps).
apply filter_imp => x.
replace (o x) with (minus (f x) (g x)).
congr (_ <= _).
by rewrite -norm_opp /minus opp_plus opp_opp plus_comm.
rewrite Ho.
rewrite /minus plus_comm plus_assoc plus_opp_l.
apply plus_zero_l.
