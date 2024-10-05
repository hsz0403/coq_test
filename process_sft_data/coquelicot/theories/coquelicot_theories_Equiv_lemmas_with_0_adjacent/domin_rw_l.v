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

Lemma domin_rw_l {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 : T -> U) (g : T -> V), is_equiv F f1 f2 -> is_domin F f1 g -> is_domin F f2 g.
Proof.
intros F FF f1 f2 g Hf Hg eps.
assert (F (fun x => norm (f1 x) <= 2 * norm (f2 x))).
eapply filter_imp.
2: apply (equiv_le_2 _ _ _ Hf).
move => /= x Hx.
by apply Hx.
clear Hf ; rename H into Hf.
specialize (Hg (pos_div_2 eps)).
generalize (filter_and _ _ Hf Hg) ; clear -FF.
apply filter_imp => x /= [Hf Hg].
apply Rle_trans with (1 := Hg).
rewrite /Rdiv Rmult_assoc.
apply Rmult_le_compat_l.
by apply Rlt_le, eps.
rewrite Rmult_comm Rle_div_l.
by rewrite Rmult_comm.
by apply Rlt_0_2.
