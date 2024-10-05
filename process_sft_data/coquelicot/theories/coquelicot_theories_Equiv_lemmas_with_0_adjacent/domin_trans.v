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

Lemma domin_trans {T} {Ku Kv Kw : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} {W : NormedModule Kw} : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g : T -> V) (h : T -> W), is_domin F f g -> is_domin F g h -> is_domin F f h.
Proof.
intros F FF f g h Hfg Hgh eps.
apply (filter_imp (fun x => (norm (h x) <= sqrt eps * norm (g x)) /\ (norm (g x) <= sqrt eps * norm (f x)))).
intros x [H0 H1].
apply Rle_trans with (1 := H0).
rewrite -{2}(sqrt_sqrt eps).
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
by apply sqrt_pos.
apply H1.
by apply Rlt_le, eps.
apply filter_and.
by apply (Hgh (mkposreal (sqrt eps) (sqrt_lt_R0 _ (cond_pos eps)))).
by apply (Hfg (mkposreal (sqrt eps) (sqrt_lt_R0 _ (cond_pos eps)))).
