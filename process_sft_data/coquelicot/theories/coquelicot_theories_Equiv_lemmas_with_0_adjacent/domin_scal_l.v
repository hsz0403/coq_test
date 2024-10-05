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

Lemma domin_scal_l : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g : T -> V) (c : Ku), (exists y, mult y c = one) -> is_domin F f g -> is_domin F (fun x => scal c (f x)) g.
Proof.
intros F FF f g c Hc H eps.
destruct Hc as [y Hc].
assert (0 < abs c).
apply Rnot_le_lt => H0.
destruct H0.
move: H0 ; by apply Rle_not_lt, abs_ge_0.
move: H0.
apply (Rmult_neq_0_reg (abs y)).
apply Rgt_not_eq.
eapply Rlt_le_trans, @abs_mult.
rewrite Hc abs_one ; by apply Rlt_0_1.
assert (0 < abs y).
apply Rmult_lt_reg_r with (abs c).
by [].
rewrite Rmult_0_l.
eapply Rlt_le_trans, @abs_mult.
rewrite Hc abs_one ; by apply Rlt_0_1.
assert (He : (0 < eps / abs y)).
apply Rdiv_lt_0_compat.
by apply eps.
by [].
move: (H (mkposreal _ He)) => /= {H}.
apply filter_imp => x Hx.
apply Rle_trans with (1 := Hx).
rewrite /Rdiv Rmult_assoc ; apply Rmult_le_compat_l.
by apply Rlt_le, eps.
rewrite -{1}(scal_one (f x)) -Hc -scal_assoc.
eapply Rle_trans.
apply Rmult_le_compat_l.
by apply Rlt_le, Rinv_0_lt_compat.
apply @norm_scal.
apply Req_le ; field.
by apply Rgt_not_eq.
