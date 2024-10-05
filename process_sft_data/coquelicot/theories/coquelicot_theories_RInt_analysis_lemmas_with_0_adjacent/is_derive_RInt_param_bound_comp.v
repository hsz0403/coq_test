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
ring.
