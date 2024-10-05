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

Lemma equiv_sym : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> V), is_equiv F f g -> is_equiv F g f.
Proof.
intros F FF f g H eps.
assert (H0 := equiv_le_2 _ _ _ H).
specialize (H (pos_div_2 eps)).
generalize (filter_and _ _ H H0) ; apply filter_imp ; clear => x [H [H0 H1]].
rewrite -norm_opp /minus opp_plus opp_opp plus_comm.
apply Rle_trans with (1 := H) ; simpl.
eapply Rle_trans.
apply Rmult_le_compat_l.
by apply Rlt_le, is_pos_div_2.
by apply H0.
apply Req_le ; field.
