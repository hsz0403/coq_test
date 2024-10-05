Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Hierarchy Seq_fct RInt PSeries.
Section Continuity.
Context {V : NormedModule R_AbsRing}.
End Continuity.
Section Derive.
Context {V : NormedModule R_AbsRing}.
End Derive.
Section Derive'.
Context {V : CompleteNormedModule R_AbsRing}.
End Derive'.
Section Comp.
Context {V : CompleteNormedModule R_AbsRing}.
End Comp.
Section RInt_comp.
Context {V : NormedModule R_AbsRing}.
End RInt_comp.
Definition PS_Int (a : nat -> R) (n : nat) : R := match n with | O => 0 | S n => a n / INR (S n) end.
Section ByParts.
Context {V : CompleteNormedModule R_AbsRing}.
End ByParts.

Lemma is_derive_RInt_param_bound_comp_aux2 : forall (f : R -> R -> R) (a : R -> R) (b x da : R), (locally x (fun y : R => ex_RInt (fun t => f y t) (a x) b)) -> (exists eps:posreal, locally x (fun y : R => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) -> is_derive a x da -> (exists eps:posreal, locally x (fun x0 : R => forall t : R, Rmin (a x-eps) b <= t <= Rmax (a x+eps) b -> ex_derive (fun u : R => f u t) x0)) -> (forall t : R, Rmin (a x) b <= t <= Rmax (a x) b -> continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> (locally_2d (fun x' t => continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) -> continuity_pt (fun t => f x t) (a x) -> is_derive (fun x : R => RInt (fun t => f x t) (a x) b) x (RInt (fun t : R => Derive (fun u => f u t) x) (a x) b+(-f x (a x))*da).
Proof.
intros f a b x da Hi [d0 Ia] Da [d1 Df] Cdf1 Cdf2 Cfa.
rewrite Rplus_comm.
apply is_derive_ext_loc with (fun x0 => plus (RInt (fun t : R => f x0 t) (a x0) (a x)) (RInt (fun t : R => f x0 t) (a x) b)).
apply RInt_Chasles_bound_comp_l_loc.
exact Hi.
now exists d0.
apply: filterdiff_continuous.
eexists.
apply Da.
apply: is_derive_plus.
eapply filterdiff_ext_lin.
apply @filterdiff_comp'_2 with (h := fun x0 y => RInt (fun t : R => f x0 t) y (a x)).
apply filterdiff_id.
apply Da.
eapply filterdiff_ext_lin.
apply (is_derive_filterdiff (fun u v => RInt (fun t0 : R => f u t0) v (a x)) x (a x) (fun u v => Derive (fun z => RInt (fun t => f z t) v (a x)) u)).
destruct Df as (d2,Df).
destruct Cdf2 as (d3,Cdf2).
destruct Ia as (d4,Ia).
exists (mkposreal _ (Rmin_stable_in_posreal (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2))) (mkposreal _ (Rmin_stable_in_posreal d3 (mkposreal _ (Rmin_stable_in_posreal d0 (pos_div_2 d4))))))).
intros [u v] [Hu Hv] ; simpl in *.
apply: Derive_correct.
eexists ; apply is_derive_RInt_param.
exists (pos_div_2 d2).
intros y Hy t Ht.
apply Df.
rewrite (double_var d2).
apply: ball_triangle Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1 := Rmin_l _ _).
apply Rmin_glb.
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply Rplus_le_reg_l with (- a x + d1); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (a x + d1).
apply Rmax_lub.
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply Rplus_le_reg_l with (- a x); ring_simplify.
left; apply cond_pos.
apply Rmax_l.
intros t Ht.
apply Cdf2.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
exists (pos_div_2 d4).
intros y Hy.
apply (ex_RInt_inside (f y)) with (a x) d0.
apply Ia.
rewrite (double_var d4).
apply: ball_triangle Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
apply is_derive_RInt' with (a x).
apply locally_singleton in Ia.
exists d0 => /= y Hy.
apply: RInt_correct.
generalize (proj1 (Rabs_lt_between' _ _ _) Hy) => {Hy} Hy.
eapply ex_RInt_Chasles.
eapply ex_RInt_Chasles, Ia.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_1, Ia.
split ; apply Rlt_le, Hy.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_2, Ia.
apply Rabs_le_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
by apply continuity_pt_filterlim, Cfa.
apply (continuity_2d_pt_filterlim (fun u v => Derive (fun z : R => RInt (fun t0 : R => f z t0) v (a x)) u)).
simpl.
apply is_derive_RInt_param_bound_comp_aux1; try easy.
exists d0; exact Ia.
exists d1.
move: Df ; apply filter_imp.
intros y H t Ht.
apply H.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rmax_l.
case => /= u v.
erewrite Derive_ext.
2: intros ; by rewrite RInt_point.
by rewrite Derive_const scal_zero_r plus_zero_l.
move => /= y ; apply Rminus_diag_uniq.
rewrite /plus /scal /opp /= /mult /=.
ring.
apply is_derive_RInt_param with (2 := Cdf1) (3 := Hi).
move: Df ; apply filter_imp.
intros y Hy t Ht; apply Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x+d1); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
Admitted.

Lemma is_derive_RInt_param_bound_comp_aux3 : forall (f : R -> R -> R) a (b : R -> R) (x db : R), (locally x (fun y : R => ex_RInt (fun t => f y t) a (b x))) -> (exists eps:posreal, locally x (fun y : R => ex_RInt (fun t => f y t) (b x - eps) (b x + eps))) -> is_derive b x db -> (exists eps:posreal, locally x (fun x0 : R => forall t : R, Rmin a (b x-eps) <= t <= Rmax a (b x+eps) -> ex_derive (fun u : R => f u t) x0)) -> (forall t : R, Rmin a (b x) <= t <= Rmax a (b x) -> continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> (locally_2d (fun x' t => continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) -> continuity_pt (fun t => f x t) (b x) -> is_derive (fun x : R => RInt (fun t => f x t) a (b x)) x (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db).
Proof.
intros f a b x db If Ib Db Df Cf1 Cf2 Cfb.
apply is_derive_ext_loc with (fun x0 => - RInt (fun t : R => f x0 t) (b x0) a).
destruct Ib as [eps Ib].
cut (locally x (fun t : R => ex_RInt (fun u => f t u) a (b t))).
apply: filter_imp.
intros y H.
apply: opp_RInt_swap.
exact: ex_RInt_swap.
assert (locally x (fun t : R => Rabs (b t - b x) <= eps)).
generalize (ex_derive_continuous b _ (ex_intro _ _ Db)).
move /filterlim_locally /(_ eps).
apply: filter_imp => t.
exact: Rlt_le.
generalize (filter_and _ _ If (filter_and _ _ Ib H)).
apply: filter_imp => t [Ht1 [Ht2 Ht3]].
apply ex_RInt_Chasles with (1 := Ht1).
apply: ex_RInt_inside Ht2 _ Ht3.
rewrite Rminus_eq_0 Rabs_R0.
apply Rlt_le, cond_pos.
evar_last.
apply: is_derive_opp.
apply: is_derive_RInt_param_bound_comp_aux2 Ib Db _ _ Cf2 Cfb.
apply: filter_imp If => y H.
now apply ex_RInt_swap.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
now rewrite Rmin_comm Rmax_comm.
intros t Ht.
apply Cf1.
now rewrite Rmin_comm Rmax_comm.
rewrite -(opp_RInt_swap _ _ a).
rewrite /opp /=.
ring.
apply ex_RInt_swap.
apply ex_RInt_continuous.
intros z Hz.
specialize (Cf1 z Hz).
apply continuity_2d_pt_filterlim in Cf1.
intros c Hc.
destruct (Cf1 c Hc) as [e He].
exists e.
intros d Hd.
apply (He (x,d)).
split.
apply ball_center.
Admitted.

Lemma is_derive_RInt_param_bound_comp : forall (f : R -> R -> R) (a b : R -> R) (x da db : R), (locally x (fun y : R => ex_RInt (fun t => f y t) (a x) (b x))) -> (exists eps:posreal, locally x (fun y : R => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) -> (exists eps:posreal, locally x (fun y : R => ex_RInt (fun t => f y t) (b x - eps) (b x + eps))) -> is_derive a x da -> is_derive b x db -> (exists eps:posreal, locally x (fun x0 : R => forall t : R, Rmin (a x-eps) (b x -eps) <= t <= Rmax (a x+eps) (b x+eps) -> ex_derive (fun u : R => f u t) x0)) -> (forall t : R, Rmin (a x) (b x) <= t <= Rmax (a x) (b x) -> continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> (locally_2d (fun x' t => continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) -> (locally_2d (fun x' t => continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) -> continuity_pt (fun t => f x t) (a x) -> continuity_pt (fun t => f x t) (b x) -> is_derive (fun x : R => RInt (fun t => f x t) (a x) (b x)) x (RInt (fun t : R => Derive (fun u => f u t) x) (a x) (b x)+(-f x (a x))*da+(f x (b x))*db).
Proof.
intros f a b x da db If Ifa Ifb Da Db Df Cf Cfa Cfb Ca Cb.
apply is_derive_ext_loc with (fun x0 : R => RInt (fun t : R => f x0 t) (a x0) (a x) + RInt (fun t : R => f x0 t) (a x) (b x0)).
apply RInt_Chasles_bound_comp_loc ; trivial.
apply @filterdiff_continuous.
eexists.
apply Da.
apply @filterdiff_continuous.
eexists.
apply Db.
eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct.
by apply locally_filter.
apply is_derive_RInt_param_bound_comp_aux2; try easy.
exists (mkposreal _ Rlt_0_1).
intros y Hy.
apply ex_RInt_point.
by apply Da.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
intros t Ht.
apply Cf.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
now right.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
now right.
apply is_derive_RInt_param_bound_comp_aux3; try easy.
by apply Db.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
rewrite RInt_point.
simpl => y.
rewrite /plus /scal /zero /= /mult /=.
Admitted.

Lemma CV_radius_Int (a : nat -> R) : CV_radius (PS_Int a) = CV_radius a.
Proof.
rewrite -CV_radius_derive.
apply CV_radius_ext.
rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
field.
Admitted.

Lemma is_RInt_PSeries (a : nat -> R) (x : R) : Rbar_lt (Rabs x) (CV_radius a) -> is_RInt (PSeries a) 0 x (PSeries (PS_Int a) x).
Proof.
move => Hx.
have H : forall y, Rmin 0 x <= y <= Rmax 0 x -> Rbar_lt (Rabs y) (CV_radius a).
move => y Hy.
apply: Rbar_le_lt_trans Hx.
apply Rabs_le_between.
split.
apply Rle_trans with (2 := proj1 Hy).
rewrite /Rabs /Rmin.
case: Rcase_abs ; case: Rle_dec => // Hx Hx' ; rewrite ?Ropp_involutive.
by apply Rlt_le.
by apply Req_le.
apply Ropp_le_cancel ; by rewrite Ropp_involutive Ropp_0.
by apply Rge_le in Hx'.
apply Rle_trans with (1 := proj2 Hy).
rewrite /Rabs /Rmax.
case: Rcase_abs ; case: Rle_dec => // Hx Hx'.
by apply Rlt_not_le in Hx'.
apply Ropp_le_cancel, Rlt_le ; by rewrite Ropp_involutive Ropp_0.
by apply Req_le.
by apply Rge_le in Hx'.
apply is_RInt_ext with (Derive (PSeries (PS_Int a))).
move => y Hy.
rewrite Derive_PSeries.
apply PSeries_ext ; rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
field.
apply Rgt_not_eq, INRp1_pos.
rewrite CV_radius_Int.
by apply H ; split ; apply Rlt_le ; apply Hy.
evar_last.
apply: is_RInt_derive.
move => y Hy.
apply Derive_correct, ex_derive_PSeries.
rewrite CV_radius_Int.
by apply H.
move => y Hy.
apply continuous_ext_loc with (PSeries a).
apply locally_interval with (Rbar_opp (CV_radius a)) (CV_radius a).
apply Rbar_opp_lt ; rewrite Rbar_opp_involutive.
apply: Rbar_le_lt_trans (H _ Hy).
apply Rabs_maj2.
apply: Rbar_le_lt_trans (H _ Hy).
apply Rle_abs.
move => z Hz Hz'.
rewrite Derive_PSeries.
apply PSeries_ext ; rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
field.
apply Rgt_not_eq, INRp1_pos.
rewrite CV_radius_Int.
apply (Rbar_abs_lt_between z) ; by split.
apply continuity_pt_filterlim, PSeries_continuity.
by apply H.
Admitted.

Lemma ex_RInt_PSeries (a : nat -> R) (x : R) : Rbar_lt (Rabs x) (CV_radius a) -> ex_RInt (PSeries a) 0 x.
Proof.
move => Hx.
exists (PSeries (PS_Int a) x).
Admitted.

Lemma RInt_PSeries (a : nat -> R) (x : R) : Rbar_lt (Rabs x) (CV_radius a) -> RInt (PSeries a) 0 x = PSeries (PS_Int a) x.
Proof.
move => Hx.
apply is_RInt_unique.
Admitted.

Lemma is_pseries_RInt (a : nat -> R) : forall x, Rbar_lt (Rabs x) (CV_radius a) -> is_pseries (PS_Int a) x (RInt (PSeries a) 0 x).
Proof.
move => x Hx.
erewrite is_RInt_unique.
apply PSeries_correct.
apply CV_radius_inside.
by rewrite CV_radius_Int.
Admitted.

Lemma is_RInt_scal_derive : forall (f : R -> R) (g : R -> V) (f' : R -> R) (g' : R -> V) (a b : R), (forall t, Rmin a b <= t <= Rmax a b -> is_derive f t (f' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> is_derive g t (g' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous f' t) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous g' t) -> is_RInt (fun t => plus (scal (f' t) (g t)) (scal (f t) (g' t))) a b (minus (scal (f b) (g b)) (scal (f a) (g a))).
Proof.
intros f g f' g' a b Df Dg Cf' Cg' If'g.
apply (is_RInt_derive (fun t => scal (f t) (g t))).
intros t Ht.
refine (_ (filterdiff_scal_fct t f g _ _ _ (Df _ Ht) (Dg _ Ht))).
intros H.
apply: filterdiff_ext_lin H _ => u.
by rewrite scal_distr_l !scal_assoc /mult /= Rmult_comm.
exact Rmult_comm.
intros t Ht.
apply: continuous_plus.
apply: continuous_scal.
now apply Cf'.
apply ex_derive_continuous.
eexists.
now apply Dg.
apply: continuous_scal.
apply: ex_derive_continuous.
eexists.
now apply Df.
Admitted.

Lemma is_RInt_scal_derive_r : forall (f : R -> R) (g : R -> V) (f' : R -> R) (g' : R -> V) (a b : R) (l : V), (forall t, Rmin a b <= t <= Rmax a b -> is_derive f t (f' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> is_derive g t (g' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous f' t) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous g' t) -> is_RInt (fun t => scal (f' t) (g t)) a b l -> is_RInt (fun t => scal (f t) (g' t)) a b (minus (minus (scal (f b) (g b)) (scal (f a) (g a))) l).
Proof.
intros f g f' g' a b l Df Dg Cf' Cg' If'g.
apply (is_RInt_ext (fun t => minus (plus (scal (f' t) (g t)) (scal (f t) (g' t))) (scal (f' t) (g t)))).
intros x H.
by rewrite /minus (plus_comm (scal (f' x) _)) -plus_assoc plus_opp_r plus_zero_r.
apply is_RInt_minus with (2 := If'g).
Admitted.

Lemma is_RInt_scal_derive_l : forall (f : R -> R) (g : R -> V) (f' : R -> R) (g' : R -> V) (a b : R) (l : V), (forall t, Rmin a b <= t <= Rmax a b -> is_derive f t (f' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> is_derive g t (g' t)) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous f' t) -> (forall t, Rmin a b <= t <= Rmax a b -> continuous g' t) -> is_RInt (fun t => scal (f t) (g' t)) a b l -> is_RInt (fun t => scal (f' t) (g t)) a b (minus (minus (scal (f b) (g b)) (scal (f a) (g a))) l).
Proof.
intros f g f' g' a b l Df Dg Cf' Cg' If'g.
apply (is_RInt_ext (fun t => minus (plus (scal (f' t) (g t)) (scal (f t) (g' t))) (scal (f t) (g' t)))).
intros x H.
by rewrite /minus -plus_assoc plus_opp_r plus_zero_r.
apply is_RInt_minus with (2 := If'g).
exact: is_RInt_scal_derive.
