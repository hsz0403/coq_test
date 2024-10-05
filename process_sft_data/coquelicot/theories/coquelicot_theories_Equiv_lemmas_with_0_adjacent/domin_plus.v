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

Lemma domin_plus : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g1 g2 : T -> V), is_domin F f g1 -> is_domin F f g2 -> is_domin F f (fun x => plus (g1 x) (g2 x)).
Proof.
intros F FF f g1 g2 Hg1 Hg2 eps.
generalize (filter_and _ _ (Hg1 (pos_div_2 eps)) (Hg2 (pos_div_2 eps))) => /= {Hg1 Hg2}.
apply filter_imp => x [Hg1 Hg2].
eapply Rle_trans.
apply @norm_triangle.
eapply Rle_trans.
apply Rplus_le_compat.
by apply Hg1.
by apply Hg2.
apply Req_le ; field.
