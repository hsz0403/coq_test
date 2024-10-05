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

Lemma equiv_trans : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> V), is_equiv F f g -> is_equiv F g h -> is_equiv F f h.
Proof.
intros F FF f g h Hfg Hgh.
apply (fun c => domin_rw_l _ _ c Hgh).
intros eps.
apply equiv_sym in Hgh.
generalize (filter_and _ _ (Hfg (pos_div_2 eps)) (Hgh (pos_div_2 eps))) => {Hfg Hgh}.
apply filter_imp => x /= [Hfg Hgh].
replace (minus (h x) (f x)) with (plus (minus (g x) (f x)) (opp (minus (g x) (h x)))).
eapply Rle_trans.
1 : by apply @norm_triangle.
rewrite norm_opp (double_var eps) Rmult_plus_distr_r.
by apply Rplus_le_compat.
rewrite /minus opp_plus opp_opp plus_comm plus_assoc.
congr (plus _ (opp (f x))).
rewrite plus_comm plus_assoc plus_opp_r.
apply plus_zero_l.
