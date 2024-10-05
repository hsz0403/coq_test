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

Lemma equiv_inv : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R), F (fun x => g x <> 0) -> is_equiv F f g -> is_equiv F (fun x => / f x) (fun x => / g x).
Proof.
intros T F FF f g Hg H.
have Hf : F (fun x => f x <> 0).
generalize (filter_and _ _ Hg (H (pos_div_2 (mkposreal _ Rlt_0_1)))) => /=.
apply filter_imp => x {Hg H} [Hg H].
case: (Req_dec (f x) 0) => Hf //.
rewrite /minus /plus /opp /= Hf Ropp_0 Rplus_0_r in H.
generalize (norm_ge_0 (g x)) (norm_eq_zero (g x)).
rewrite /zero /=.
lra.
apply equiv_sym in H.
move => eps.
generalize (filter_and _ _ (filter_and _ _ Hf Hg) (H eps)).
clear -FF.
apply filter_imp.
intros x [[Hf Hg] H].
rewrite /norm /= /abs /minus /plus /opp /=.
replace (/ g x + - / f x) with ((f x - g x) / (f x * g x)).
rewrite Rabs_div ?Rabs_Rinv ?Rabs_mult //.
apply Rle_div_l.
apply Rmult_lt_0_compat ; by apply Rabs_pos_lt.
field_simplify ; rewrite ?Rdiv_1.
by [].
by apply Rabs_no_R0.
by apply Rmult_integral_contrapositive_currified.
field ; by split.
