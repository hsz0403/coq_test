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
apply Hd.
