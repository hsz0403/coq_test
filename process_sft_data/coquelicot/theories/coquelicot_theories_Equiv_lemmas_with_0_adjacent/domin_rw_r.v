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

Lemma domin_rw_r {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g1 g2 : T -> V), is_equiv F g1 g2 -> is_domin F f g1 -> is_domin F f g2.
Proof.
intros F FF f g1 g2 Hg Hf eps.
assert (F (fun x => norm (g2 x) <= 2 * norm (g1 x))).
eapply filter_imp.
2: apply (equiv_le_2 _ _ _ Hg).
move => /= x Hx.
by apply Hx.
clear Hg ; rename H into Hg.
specialize (Hf (pos_div_2 eps)).
generalize (filter_and _ _ Hf Hg) ; clear -FF.
apply filter_imp => x /= [Hf Hg].
apply Rle_trans with (1 := Hg).
rewrite Rmult_comm Rle_div_r.
apply Rle_trans with (1 := Hf).
right ; rewrite /Rdiv ; ring.
by apply Rlt_0_2.
