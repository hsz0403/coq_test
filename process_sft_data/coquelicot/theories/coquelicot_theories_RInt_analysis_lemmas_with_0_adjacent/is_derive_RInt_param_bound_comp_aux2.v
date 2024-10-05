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
left; apply cond_pos.
