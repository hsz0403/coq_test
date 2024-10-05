Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Open Scope R_scope.
Inductive Rbar := | Finite : R -> Rbar | p_infty : Rbar | m_infty : Rbar.
Definition real (x : Rbar) := match x with | Finite x => x | _ => 0 end.
Coercion Finite : R >-> Rbar.
Coercion real : Rbar >-> R.
Definition is_finite (x : Rbar) := Finite (real x) = x.
Definition Rbar_lt (x y : Rbar) : Prop := match x,y with | p_infty, _ | _, m_infty => False | m_infty, _ | _, p_infty => True | Finite x, Finite y => Rlt x y end.
Definition Rbar_le (x y : Rbar) : Prop := match x,y with | m_infty, _ | _, p_infty => True | p_infty, _ | _, m_infty => False | Finite x, Finite y => Rle x y end.
Definition Rbar_opp (x : Rbar) := match x with | Finite x => Finite (-x) | p_infty => m_infty | m_infty => p_infty end.
Definition Rbar_plus' (x y : Rbar) := match x,y with | p_infty, m_infty | m_infty, p_infty => None | p_infty, _ | _, p_infty => Some p_infty | m_infty, _ | _, m_infty => Some m_infty | Finite x', Finite y' => Some (Finite (x' + y')) end.
Definition Rbar_plus (x y : Rbar) := match Rbar_plus' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_plus !x !y /.
Definition is_Rbar_plus (x y z : Rbar) : Prop := Rbar_plus' x y = Some z.
Definition ex_Rbar_plus (x y : Rbar) : Prop := match Rbar_plus' x y with Some _ => True | None => False end.
Arguments ex_Rbar_plus !x !y /.
Definition Rbar_minus (x y : Rbar) := Rbar_plus x (Rbar_opp y).
Arguments Rbar_minus !x !y /.
Definition is_Rbar_minus (x y z : Rbar) : Prop := is_Rbar_plus x (Rbar_opp y) z.
Definition ex_Rbar_minus (x y : Rbar) : Prop := ex_Rbar_plus x (Rbar_opp y).
Arguments ex_Rbar_minus !x !y /.
Definition Rbar_inv (x : Rbar) : Rbar := match x with | Finite x => Finite (/x) | _ => Finite 0 end.
Definition Rbar_mult' (x y : Rbar) := match x with | Finite x => match y with | Finite y => Some (Finite (x * y)) | p_infty => match (Rle_dec 0 x) with | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some p_infty | right _ => None end | right _ => Some m_infty end | m_infty => match (Rle_dec 0 x) with | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some m_infty | right _ => None end | right _ => Some p_infty end end | p_infty => match y with | Finite y => match (Rle_dec 0 y) with | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some p_infty | right _ => None end | right _ => Some m_infty end | p_infty => Some p_infty | m_infty => Some m_infty end | m_infty => match y with | Finite y => match (Rle_dec 0 y) with | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some m_infty | right _ => None end | right _ => Some p_infty end | p_infty => Some m_infty | m_infty => Some p_infty end end.
Definition Rbar_mult (x y : Rbar) := match Rbar_mult' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_mult !x !y /.
Definition is_Rbar_mult (x y z : Rbar) : Prop := Rbar_mult' x y = Some z.
Definition ex_Rbar_mult (x y : Rbar) : Prop := match x with | Finite x => match y with | Finite y => True | p_infty => x <> 0 | m_infty => x <> 0 end | p_infty => match y with | Finite y => y <> 0 | p_infty => True | m_infty => True end | m_infty => match y with | Finite y => y <> 0 | p_infty => True | m_infty => True end end.
Arguments ex_Rbar_mult !x !y /.
Definition Rbar_mult_pos (x : Rbar) (y : posreal) := match x with | Finite x => Finite (x*y) | _ => x end.
Definition Rbar_div (x y : Rbar) : Rbar := Rbar_mult x (Rbar_inv y).
Arguments Rbar_div !x !y /.
Definition is_Rbar_div (x y z : Rbar) : Prop := is_Rbar_mult x (Rbar_inv y) z.
Definition ex_Rbar_div (x y : Rbar) : Prop := ex_Rbar_mult x (Rbar_inv y).
Arguments ex_Rbar_div !x !y /.
Definition Rbar_div_pos (x : Rbar) (y : posreal) := match x with | Finite x => Finite (x/y) | _ => x end.
Definition Rbar_min (x y : Rbar) : Rbar := match x, y with | z, p_infty | p_infty, z => z | _ , m_infty | m_infty, _ => m_infty | Finite x, Finite y => Rmin x y end.
Definition Rbar_abs (x : Rbar) := match x with | Finite x => Finite (Rabs x) | _ => p_infty end.

Lemma is_Rbar_mult_p_infty_pos (x : Rbar) : Rbar_lt 0 x -> is_Rbar_mult p_infty x p_infty.
Proof.
case: x => [x | | ] // Hx.
unfold is_Rbar_mult, Rbar_mult'.
case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
Admitted.

Lemma is_Rbar_mult_p_infty_neg (x : Rbar) : Rbar_lt x 0 -> is_Rbar_mult p_infty x m_infty.
Proof.
case: x => [x | | ] // Hx.
unfold is_Rbar_mult, Rbar_mult'.
Admitted.

Lemma is_Rbar_mult_m_infty_pos (x : Rbar) : Rbar_lt 0 x -> is_Rbar_mult m_infty x m_infty.
Proof.
case: x => [x | | ] // Hx.
unfold is_Rbar_mult, Rbar_mult'.
case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
Admitted.

Lemma is_Rbar_mult_m_infty_neg (x : Rbar) : Rbar_lt x 0 -> is_Rbar_mult m_infty x p_infty.
Proof.
case: x => [x | | ] // Hx.
unfold is_Rbar_mult, Rbar_mult'.
Admitted.

Lemma is_Rbar_div_p_infty (x : R) : is_Rbar_div x p_infty 0.
Proof.
apply (f_equal (@Some _)).
Admitted.

Lemma is_Rbar_div_m_infty (x : R) : is_Rbar_div x m_infty 0.
Proof.
apply (f_equal (@Some _)).
Admitted.

Lemma Rbar_mult_pos_eq (x y : Rbar) (z : posreal) : x = y <-> (Rbar_mult_pos x z) = (Rbar_mult_pos y z).
Proof.
case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ; split => //= H ; apply Rbar_finite_eq in H.
by rewrite H.
Admitted.

Lemma Rbar_mult_pos_lt (x y : Rbar) (z : posreal) : Rbar_lt x y <-> Rbar_lt (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ; split => //= H.
apply (Rmult_lt_compat_r (z)) => //.
Admitted.

Lemma Rbar_mult_pos_le (x y : Rbar) (z : posreal) : Rbar_le x y <-> Rbar_le (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ; split => //= H.
apply Rmult_le_compat_r with (2 := H).
now apply Rlt_le.
Admitted.

Lemma Rbar_div_pos_eq (x y : Rbar) (z : posreal) : x = y <-> (Rbar_div_pos x z) = (Rbar_div_pos y z).
Proof.
case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ; split => //= H ; apply Rbar_finite_eq in H.
by rewrite H.
Admitted.

Lemma Rbar_div_pos_le (x y : Rbar) (z : posreal) : Rbar_le x y <-> Rbar_le (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ; split => //= H.
apply Rmult_le_compat_r with (2 := H).
now apply Rlt_le, Rinv_0_lt_compat.
apply Rmult_le_reg_r with (2 := H).
Admitted.

Lemma Rbar_lt_locally (a b : Rbar) (x : R) : Rbar_lt a x -> Rbar_lt x b -> exists delta : posreal, forall y, Rabs (y - x) < delta -> Rbar_lt a y /\ Rbar_lt y b.
Proof.
case: a => [ a /= Ha | | _ ] //= ; (try apply Rminus_lt_0 in Ha) ; case: b => [ b Hb | _ | ] //= ; (try apply Rminus_lt_0 in Hb).
assert (0 < Rmin (x - a) (b - x)).
by apply Rmin_case.
exists (mkposreal _ H) => y /= Hy ; split.
apply Rplus_lt_reg_r with (-x).
replace (a+-x) with (-(x-a)) by ring.
apply (Rabs_lt_between (y - x)).
apply Rlt_le_trans with (1 := Hy).
by apply Rmin_l.
apply Rplus_lt_reg_r with (-x).
apply (Rabs_lt_between (y - x)).
apply Rlt_le_trans with (1 := Hy).
by apply Rmin_r.
exists (mkposreal _ Ha) => y /= Hy ; split => //.
apply Rplus_lt_reg_r with (-x).
replace (a+-x) with (-(x-a)) by ring.
by apply (Rabs_lt_between (y - x)).
exists (mkposreal _ Hb) => y /= Hy ; split => //.
apply Rplus_lt_reg_r with (-x).
by apply (Rabs_lt_between (y - x)).
Admitted.

Lemma Rbar_min_comm (x y : Rbar) : Rbar_min x y = Rbar_min y x.
Proof.
case: x => [x | | ] //= ; case: y => [y | | ] //=.
Admitted.

Lemma Rbar_min_r (x y : Rbar) : Rbar_le (Rbar_min x y) y.
Proof.
case: x => [x | | ] //= ; case: y => [y | | ] //=.
by apply Rmin_r.
Admitted.

Lemma Rbar_min_l (x y : Rbar) : Rbar_le (Rbar_min x y) x.
Proof.
rewrite Rbar_min_comm.
Admitted.

Lemma Rbar_min_case (x y : Rbar) (P : Rbar -> Type) : P x -> P y -> P (Rbar_min x y).
Proof.
case: x => [x | | ] //= ; case: y => [y | | ] //=.
Admitted.

Lemma Rbar_min_case_strong (r1 r2 : Rbar) (P : Rbar -> Type) : (Rbar_le r1 r2 -> P r1) -> (Rbar_le r2 r1 -> P r2) -> P (Rbar_min r1 r2).
Proof.
case: r1 => [x | | ] //= ; case: r2 => [y | | ] //= Hx Hy ; (try by apply Hx) ; (try by apply Hy).
Admitted.

Lemma Rbar_abs_lt_between (x y : Rbar) : Rbar_lt (Rbar_abs x) y <-> (Rbar_lt (Rbar_opp y) x /\ Rbar_lt x y).
Proof.
case: x => [x | | ] ; case: y => [y | | ] /= ; try by intuition.
Admitted.

Lemma Rbar_abs_opp (x : Rbar) : Rbar_abs (Rbar_opp x) = Rbar_abs x.
Proof.
case: x => [x | | ] //=.
Admitted.

Lemma Rbar_abs_pos (x : Rbar) : Rbar_le 0 x -> Rbar_abs x = x.
Proof.
case: x => [x | | ] //= Hx.
Admitted.

Lemma Rbar_div_pos_lt (x y : Rbar) (z : posreal) : Rbar_lt x y <-> Rbar_lt (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ; split => //= H.
apply (Rmult_lt_compat_r (/z)) => // ; by apply Rinv_0_lt_compat.
apply (Rmult_lt_reg_r (/z)) => // ; by apply Rinv_0_lt_compat.
