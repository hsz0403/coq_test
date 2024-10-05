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

Lemma is_derive_RInt_param : forall f a b x, locally x (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) -> (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) -> locally x (fun y => ex_RInt (fun t => f y t) a b) -> is_derive (fun x => RInt (fun t => f x t) a b) x (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x H1 H2 H3.
apply is_derive_RInt_param_aux; try easy.
apply ex_RInt_Reals_1.
clear H1 H3.
wlog: a b H2 / a < b => H.
case (total_order_T a b).
intro Y; case Y.
now apply H.
intros Heq; rewrite Heq.
apply RiemannInt_P7.
intros Y.
apply RiemannInt_P1.
apply H.
intros; apply H2.
rewrite Rmin_comm Rmax_comm.
exact H0.
exact Y.
rewrite Rmin_left in H2.
2: now left.
rewrite Rmax_right in H2.
2: now left.
apply continuity_implies_RiemannInt.
now left.
intros y Hy eps Heps.
destruct (H2 _ Hy (mkposreal eps Heps)) as (d,Hd).
simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist; simpl.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
