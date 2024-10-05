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

Lemma Derive_partial_derive_aux2: forall p k f x y, locally_2d (ex_diff_n f (p+S k)) x y -> partial_derive 0 1 (partial_derive p k f) x y = partial_derive p (S k) f x y.
Proof.
intros p; induction p.
intros; easy.
intros k f x y Y.
apply sym_eq.
apply trans_eq with (partial_derive p 0 (partial_derive 1 (S k) f) x y).
rewrite partial_derive_add_zero.
rewrite plus_0_l.
replace (S p) with (p+1)%nat by apply Arith.Plus.plus_comm.
easy.
now left.
apply trans_eq with (partial_derive p 0 (partial_derive 0 (S k) (partial_derive 1 0 f)) x y).
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=Y).
apply locally_2d_forall.
intros u v H.
apply Derive_partial_derive_aux1.
apply locally_2d_impl with (2:=H).
apply locally_2d_forall.
intros u'' v''.
apply ex_diff_n_m.
omega.
apply trans_eq with (partial_derive p (S k) (partial_derive 1 0 f) x y).
rewrite partial_derive_add_zero.
now rewrite plus_0_l plus_0_r.
now right.
rewrite - IHp.
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=Y).
apply locally_2d_forall.
intros u v H.
apply trans_eq with (partial_derive p 0 (partial_derive 0 k (partial_derive 1 0 f)) u v).
rewrite (partial_derive_add_zero _ _ 0%nat).
now rewrite plus_0_l plus_0_r.
now right.
apply trans_eq with (partial_derive p 0 (partial_derive 1 k f) u v).
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u' v' H'.
apply sym_eq.
apply Derive_partial_derive_aux1.
apply locally_2d_impl with (2:=H').
apply locally_2d_forall.
intros u'' v''.
apply ex_diff_n_m.
apply le_plus_r.
rewrite partial_derive_add_zero.
rewrite plus_0_l.
replace (S p) with (p+1)%nat by apply Arith.Plus.plus_comm.
easy.
now left.
apply locally_2d_impl with (2:=Y).
apply locally_2d_forall.
intros u'' v''.
replace (p+ S k)%nat with ((S p+S k)-(1+0))%nat.
apply ex_diff_n_deriv.
rewrite plus_0_r.
apply le_plus_trans; apply lt_le_S; apply lt_0_Sn.
rewrite plus_0_r.
omega.
