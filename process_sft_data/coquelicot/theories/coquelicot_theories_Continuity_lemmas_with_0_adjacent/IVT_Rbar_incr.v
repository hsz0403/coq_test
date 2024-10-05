Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Compactness Lim_seq.
Definition is_lim (f : R -> R) (x l : Rbar) := filterlim f (Rbar_locally' x) (Rbar_locally l).
Definition is_lim' (f : R -> R) (x l : Rbar) := match l with | Finite l => forall eps : posreal, Rbar_locally' x (fun y => Rabs (f y - l) < eps) | p_infty => forall M : R, Rbar_locally' x (fun y => M < f y) | m_infty => forall M : R, Rbar_locally' x (fun y => f y < M) end.
Definition ex_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_lim f x l.
Definition ex_finite_lim (f : R -> R) (x : Rbar) := exists l : R, is_lim f x l.
Definition Lim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).
Definition continuity_2d_pt f x y := forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.
Section Continuity.
Context {T U : UniformSpace}.
Definition continuous_on (D : T -> Prop) (f : T -> U) := forall x, D x -> filterlim f (within D (locally x)) (locally (f x)).
Definition continuous (f : T -> U) (x : T) := filterlim f (locally x) (locally (f x)).
End Continuity.
Section Continuity_op.
Context {U : UniformSpace} {K : AbsRing} {V : NormedModule K}.
End Continuity_op.
Section UnifCont.
Context {V : UniformSpace}.
End UnifCont.
Section UnifCont_N.
Context {K : AbsRing} {V : NormedModule K}.
End UnifCont_N.

Lemma IVT_Rbar_incr (f : R -> R) (a b la lb : Rbar) (y : R) : is_lim f a la -> is_lim f b lb -> (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> continuity_pt f x) -> Rbar_lt a b -> Rbar_lt la y /\ Rbar_lt y lb -> {x : R | Rbar_lt a x /\ Rbar_lt x b /\ f x = y}.
Proof.
intros Hfa Hfb Cf Hab Hy.
assert (Hb' : exists b' : R, Rbar_lt b' b /\ is_upper_bound (fun x => Rbar_lt a x /\ Rbar_lt x b /\ f x <= y) b').
{
assert (Hfb' : Rbar_locally' b (fun x => y < f x)).
apply Hfb.
now apply (open_Rbar_gt' _ y).
clear -Hab Hfb'.
destruct b as [b| |].
-
destruct Hfb' as [eps He].
exists (b - eps).
split.
apply Rminus_lt_0.
replace (b - (b - eps)) with (pos eps) by ring.
apply cond_pos.
intros u [_ [H1 H2]].
apply Rnot_lt_le.
intros Hu.
apply Rle_not_lt with (1 := H2).
apply He.
apply Rabs_lt_between'.
split.
exact Hu.
apply Rlt_le_trans with (1 := H1).
apply Rlt_le.
apply Rminus_lt_0.
replace (b + eps - b) with (pos eps) by ring.
apply cond_pos.
now apply Rlt_not_eq.
-
destruct Hfb' as [M HM].
exists M.
repeat split.
intros u [_ [H1 H2]].
apply Rnot_lt_le.
intros Hu.
apply Rle_not_lt with (1 := H2).
now apply HM.
-
now destruct a.
}
assert (Hex : exists x : R, Rbar_lt a x /\ Rbar_lt x b /\ f x <= y).
{
assert (Hfa' : Rbar_locally' a (fun x => Rbar_lt x b /\ f x < y)).
apply filter_and.
apply Rbar_locally'_le.
now apply open_Rbar_lt'.
apply (Hfa (fun u => u < y)).
now apply (open_Rbar_lt' _ y).
clear -Hab Hfa'.
destruct a as [a| |].
-
destruct Hfa' as [eps He].
exists (a + eps / 2).
assert (Ha : a < a + eps / 2).
apply Rminus_lt_0.
replace (a + eps / 2 - a) with (eps / 2) by ring.
apply is_pos_div_2.
split.
exact Ha.
assert (H : Rbar_lt (a + eps / 2) b /\ (f (a + eps / 2) < y)).
apply He.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (a + eps / 2 + - a) with (eps / 2) by ring.
rewrite Rabs_pos_eq.
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_le.
apply is_pos_div_2.
now apply Rgt_not_eq.
destruct H as [H1 H2].
split.
exact H1.
now apply Rlt_le.
-
easy.
-
destruct Hfa' as [M HM].
exists (M - 1).
assert (H : Rbar_lt (M - 1) b /\ f (M - 1) < y).
apply HM.
apply Rminus_lt_0.
replace (M - (M - 1)) with 1 by ring.
apply Rlt_0_1.
destruct H as [H1 H2].
repeat split.
exact H1.
now apply Rlt_le.
}
destruct (completeness (fun x => Rbar_lt a x /\ Rbar_lt x b /\ f x <= y)) as [x [Hub Hlub]].
destruct Hb' as [b' Hb'].
now exists b'.
exact Hex.
exists x.
destruct Hb' as [b' [Hb Hb']].
destruct Hex as [x' Hx'].
assert (Hax : Rbar_lt a x).
apply Rbar_lt_le_trans with x'.
apply Hx'.
now apply Hub.
assert (Hxb : Rbar_lt x b).
apply Rbar_le_lt_trans with b'.
now apply Hlub.
exact Hb.
repeat split ; try assumption.
specialize (Cf _ Hax Hxb).
apply continuity_pt_filterlim in Cf.
destruct (total_order_T (f x) y) as [[H|H]|H].
-
assert (H': locally x (fun u => (Rbar_lt a u /\ Rbar_lt u b) /\ f u < y)).
apply filter_and.
apply filter_and.
now apply open_Rbar_gt.
now apply open_Rbar_lt.
apply (Cf (fun u => u < y)).
now apply open_lt.
destruct H' as [eps H'].
elim Rle_not_lt with x (x + eps / 2).
apply Hub.
destruct (H' (x + eps / 2)) as [[H1 H2] H3].
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (x + eps / 2 + - x) with (eps / 2) by ring.
rewrite Rabs_pos_eq.
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_le.
apply is_pos_div_2.
split.
exact H1.
split.
exact H2.
now apply Rlt_le.
apply Rminus_lt_0.
replace (x + eps / 2 - x) with (eps / 2) by ring.
apply is_pos_div_2.
-
exact H.
-
assert (H': locally x (fun u => y < f u)).
apply (Cf (fun u => y < u)).
now apply open_gt.
destruct H' as [eps H'].
elim Rle_not_lt with (x - eps) x.
apply Hlub.
intros u Hfu.
apply Rnot_lt_le.
intros Hu.
apply Rle_not_lt with (1 := proj2 (proj2 Hfu)).
apply H'.
apply Rabs_lt_between'.
split.
exact Hu.
apply Rle_lt_trans with (1 := Hub u Hfu).
apply Rminus_lt_0.
replace (x + eps - x) with (pos eps) by ring.
apply cond_pos.
apply Rminus_lt_0.
replace (x - (x - eps)) with (pos eps) by ring.
apply cond_pos.
