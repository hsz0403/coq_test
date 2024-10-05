Require Import Reals Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Hierarchy Continuity Derive.
Definition differentiable_pt_lim (f : R -> R -> R) (x y : R) (lx ly : R) := forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y - (lx * (u - x) + ly * (v - y))) <= eps * Rmax (Rabs (u - x)) (Rabs (v - y))) x y.
Definition differentiable_pt (f : R -> R -> R) (x y : R) := exists lx, exists ly, differentiable_pt_lim f x y lx ly.
Definition partial_derive (m k : nat) (f : R -> R -> R) : R -> R -> R := fun x y => Derive_n (fun t => Derive_n (fun z => f t z) k y) m x.
Definition differential (p : nat) (f : R -> R -> R) (x y dx dy : R) : R := sum_f_R0 (fun m => C p m * partial_derive m (p - m)%nat f x y * dx ^ m * dy ^ (p - m)%nat) p.
Definition DL_pol (n : nat) (f : R -> R -> R) (x y dx dy : R) : R := sum_f_R0 (fun p => differential p f x y dx dy / INR (fact p)) n.
Fixpoint ex_diff_n f n x y := continuity_2d_pt f x y /\ match n with | O => True | S n => ex_derive (fun z => f z y) x /\ ex_derive (fun z => f x z) y /\ ex_diff_n (fun u v => Derive (fun z => f z v) u) n x y /\ ex_diff_n (fun u v => Derive (fun z => f u z) v) n x y end.
Definition DL_regular_n f m x y := exists D, locally_2d (fun u v => Rabs (f u v - DL_pol m f x y (u-x) (v-y)) <= D * (Rmax (Rabs (u-x)) (Rabs (v-y))) ^ (S m)) x y.

Lemma Derive_partial_derive_aux1: forall p f x y, locally_2d (ex_diff_n f (S p)) x y -> partial_derive 1 p f x y = partial_derive 0 p (partial_derive 1 0 f) x y.
Proof.
intros p; induction p.
intros f x y H.
unfold partial_derive; now simpl.
intros f x y H.
apply trans_eq with (partial_derive 1 p (partial_derive 0 1 f) x y).
unfold partial_derive.
simpl.
apply Derive_ext.
intros t.
apply trans_eq with (Derive_n (Derive_n (fun z : R => f t z) p) 1 y).
reflexivity.
rewrite Derive_n_comp.
rewrite Arith.Plus.plus_comm.
rewrite -Derive_n_comp.
reflexivity.
rewrite IHp.
apply trans_eq with (partial_derive 0 p (partial_derive 0 1 (partial_derive 1 0 f)) x y).
unfold partial_derive.
simpl.
apply Derive_n_ext_loc.
cut (locally_2d (fun u v => Derive (fun x0 : R => Derive (fun x1 : R => f x0 x1) v) u = Derive (fun x0 : R => Derive (fun x1 : R => f x1 x0) u) v) x y).
apply locally_2d_1d_const_x.
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H1.
apply Schwarz.
apply locally_2d_impl with (2:=H1).
apply locally_2d_forall.
intros u' v' H2.
split.
apply H2.
split.
apply H2.
simpl in H2; destruct H2 as (T1&T2&T3&T4&T5).
split.
apply T5.
apply T4.
apply locally_2d_singleton in H1.
simpl in H1; destruct H1 as (T1&T2&T3&T4&T5).
destruct T5 as (Y1&Y2&Y3&Y4&Y5).
clear - Y4.
case p in Y4; simpl in Y4; apply Y4.
apply locally_2d_singleton in H1.
simpl in H1; destruct H1 as (T1&T2&T3&T4&T5).
destruct T4 as (Y1&Y2&Y3&Y4&Y5).
clear - Y5.
case p in Y5; simpl in Y5; apply Y5.
unfold partial_derive.
simpl.
apply trans_eq with (Derive_n (Derive_n (fun z => Derive (fun x0 => f x0 z) x) p) 1 y).
rewrite Derive_n_comp.
rewrite Arith.Plus.plus_comm.
rewrite -Derive_n_comp.
reflexivity.
reflexivity.
apply locally_2d_impl with (2:=H).
apply locally_2d_forall.
intros u v.
pattern (S p) at 2; replace (S p) with (S (S p) -(0+1))%nat.
apply ex_diff_n_deriv.
rewrite plus_0_l.
apply lt_le_S; apply lt_0_Sn.
rewrite plus_0_l.
omega.
