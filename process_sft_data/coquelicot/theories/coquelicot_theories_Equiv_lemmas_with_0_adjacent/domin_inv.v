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

Lemma domin_inv : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R), F (fun x => g x <> 0) -> is_domin F f g -> is_domin F (fun x => / g x) (fun x => / f x).
Proof.
intros T F FF f g Hg H eps.
have Hf : F (fun x => f x <> 0).
generalize (filter_and _ _ Hg (H (mkposreal _ Rlt_0_1))) => /=.
apply filter_imp => x {Hg H} [Hg H].
case: (Req_dec (f x) 0) => Hf.
rewrite /norm /= /abs /= Hf Rabs_R0 Rmult_0_r in H.
apply Rlt_not_le in H.
move => _ ; apply H.
by apply Rabs_pos_lt.
by [].
generalize (filter_and _ _ (H eps) (filter_and _ _ Hf Hg)) => {H Hf Hg}.
apply filter_imp => x [H [Hf Hg]].
rewrite /norm /= /abs /= ?Rabs_Rinv => //.
replace (/ Rabs (f x)) with (Rabs (g x) / (Rabs (f x) * Rabs (g x))) by (field ; split ; by apply Rabs_no_R0).
replace (eps * / Rabs (g x)) with (eps * Rabs (f x) / (Rabs (f x) * Rabs (g x))) by (field ; split ; by apply Rabs_no_R0).
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat ; apply Rabs_pos_lt => //.
by apply H.
