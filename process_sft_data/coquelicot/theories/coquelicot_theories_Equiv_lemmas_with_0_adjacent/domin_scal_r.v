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

Lemma domin_scal_r : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g : T -> V) (c : Kv), is_domin F f g -> is_domin F f (fun x => scal c (g x)).
Proof.
intros F FF f g c H.
case: (Req_dec (abs c) 0) => Hc.
move => eps /=.
apply filter_imp with (2 := filter_true) => x _.
eapply Rle_trans.
apply @norm_scal.
rewrite Hc Rmult_0_l.
apply Rmult_le_pos.
by apply Rlt_le, eps.
by apply norm_ge_0.
destruct (abs_ge_0 c) => //.
clear Hc ; rename H0 into Hc.
move => eps /=.
assert (He : 0 < eps / abs c).
apply Rdiv_lt_0_compat.
by apply eps.
by apply Hc.
move: (H (mkposreal _ He)) => /= {H}.
apply filter_imp => x H.
eapply Rle_trans.
apply @norm_scal.
rewrite Rmult_comm ; apply Rle_div_r.
by [].
apply Rle_trans with (1 := H).
apply Req_le ; rewrite /Rdiv ; ring.
by apply sym_eq in H0.
