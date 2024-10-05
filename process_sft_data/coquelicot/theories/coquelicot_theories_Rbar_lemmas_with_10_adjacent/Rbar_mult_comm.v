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

Lemma Rbar_plus_0_l (x : Rbar) : Rbar_plus (Finite 0) x = x.
Proof.
Admitted.

Lemma Rbar_plus_comm (x y : Rbar) : Rbar_plus x y = Rbar_plus y x.
Proof.
case x ; case y ; intuition.
simpl.
Admitted.

Lemma Rbar_plus_lt_compat (a b c d : Rbar) : Rbar_lt a b -> Rbar_lt c d -> Rbar_lt (Rbar_plus a c) (Rbar_plus b d).
Proof.
Admitted.

Lemma Rbar_plus_le_compat (a b c d : Rbar) : Rbar_le a b -> Rbar_le c d -> Rbar_le (Rbar_plus a c) (Rbar_plus b d).
Proof.
case: a => [a | | ] // ; case: b => [b | | ] // ; case: c => [c | | ] // ; case: d => [d | | ] //.
apply Rplus_le_compat.
intros _ _.
apply Rle_refl.
intros _ _.
Admitted.

Lemma Rbar_plus_opp (x y : Rbar) : Rbar_plus (Rbar_opp x) (Rbar_opp y) = Rbar_opp (Rbar_plus x y).
Proof.
Admitted.

Lemma Rbar_minus_eq_0 (x : Rbar) : Rbar_minus x x = 0.
Proof.
Admitted.

Lemma Rbar_opp_minus (x y : Rbar) : Rbar_opp (Rbar_minus x y) = Rbar_minus y x.
Proof.
case: x => [x | | ] ; case: y => [y | | ] //=.
by rewrite Ropp_minus_distr'.
by rewrite Ropp_0.
Admitted.

Lemma Rbar_inv_opp (x : Rbar) : x <> 0 -> Rbar_inv (Rbar_opp x) = Rbar_opp (Rbar_inv x).
Proof.
case: x => [x | | ] /= Hx.
rewrite Ropp_inv_permute => //.
contradict Hx.
by rewrite Hx.
by rewrite Ropp_0.
Admitted.

Lemma Rbar_mult'_comm (x y : Rbar) : Rbar_mult' x y = Rbar_mult' y x.
Proof.
case: x => [x | | ] ; case: y => [y | | ] //=.
Admitted.

Lemma Rbar_mult'_opp_r (x y : Rbar) : Rbar_mult' x (Rbar_opp y) = match Rbar_mult' x y with Some z => Some (Rbar_opp z) | None => None end.
Proof.
case: x => [x | | ] ; case: y => [y | | ] //= ; (try case: Rle_dec => Hx //=) ; (try case: Rle_lt_or_eq_dec => //= Hx0).
by rewrite Ropp_mult_distr_r_reverse.
rewrite -Ropp_0 in Hx0.
apply Ropp_lt_cancel in Hx0.
case Rle_dec => Hy //=.
now elim Rle_not_lt with (1 := Hy).
case Rle_dec => Hy //=.
case Rle_lt_or_eq_dec => Hy0 //=.
elim Rlt_not_le with (1 := Hy0).
apply Ropp_le_cancel.
by rewrite Ropp_0.
elim Hy.
apply Ropp_le_cancel.
rewrite -Hx0 Ropp_0.
apply Rle_refl.
case Rle_dec => Hy //=.
case Rle_lt_or_eq_dec => Hy0 //=.
elim Hx.
rewrite -Hy0 Ropp_0.
apply Rle_refl.
elim Hx.
rewrite -Ropp_0.
apply Ropp_le_contravar.
apply Rlt_le.
now apply Rnot_le_lt.
case Rle_dec => Hy //=.
elim Rlt_not_le with (1 := Hx0).
rewrite -Ropp_0.
now apply Ropp_le_contravar.
case Rle_dec => Hy //=.
case Rle_lt_or_eq_dec => Hy0 //=.
elim Rlt_not_le with (1 := Hy0).
apply Ropp_le_cancel.
rewrite -Hx0 Ropp_0.
apply Rle_refl.
elim Hy.
apply Ropp_le_cancel.
rewrite -Hx0 Ropp_0.
apply Rle_refl.
case Rle_dec => Hy //=.
case Rle_lt_or_eq_dec => Hy0 //=.
elim Hx.
rewrite -Hy0 Ropp_0.
apply Rle_refl.
elim Hx.
rewrite -Ropp_0.
apply Ropp_le_contravar.
apply Rlt_le.
Admitted.

Lemma Rbar_mult_opp_r (x y : Rbar) : Rbar_mult x (Rbar_opp y) = (Rbar_opp (Rbar_mult x y)).
Proof.
unfold Rbar_mult.
rewrite Rbar_mult'_opp_r.
case Rbar_mult' => //=.
Admitted.

Lemma Rbar_mult_opp_l (x y : Rbar) : Rbar_mult (Rbar_opp x) y = Rbar_opp (Rbar_mult x y).
Proof.
rewrite ?(Rbar_mult_comm _ y).
Admitted.

Lemma Rbar_mult_opp (x y : Rbar) : Rbar_mult (Rbar_opp x) (Rbar_opp y) = Rbar_mult x y.
Proof.
Admitted.

Lemma Rbar_mult_0_l (x : Rbar) : Rbar_mult 0 x = 0.
Proof.
case: x => [x | | ] //=.
by rewrite Rmult_0_l.
case: Rle_dec (Rle_refl 0) => // H _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
case: Rle_dec (Rle_refl 0) => // H _.
Admitted.

Lemma Rbar_mult_0_r (x : Rbar) : Rbar_mult x 0 = 0.
Proof.
Admitted.

Lemma Rbar_mult_eq_0 (y x : Rbar) : Rbar_mult x y = 0 -> x = 0 \/ y = 0.
Proof.
case: x => [x | | ] //= ; case: y => [y | | ] //= ; (try case: Rle_dec => //= H) ; (try case: Rle_lt_or_eq_dec => //=) ; (try (left ; by apply f_equal)) ; (try (right ; by apply f_equal)).
intros H.
apply (f_equal real) in H.
simpl in H.
apply Rmult_integral in H ; case: H => ->.
by left.
Admitted.

Lemma ex_Rbar_mult_sym (x y : Rbar) : ex_Rbar_mult x y -> ex_Rbar_mult y x.
Proof.
Admitted.

Lemma ex_Rbar_mult_opp_l (x y : Rbar) : ex_Rbar_mult x y -> ex_Rbar_mult (Rbar_opp x) y.
Proof.
Admitted.

Lemma ex_Rbar_mult_opp_r (x y : Rbar) : ex_Rbar_mult x y -> ex_Rbar_mult x (Rbar_opp y).
Proof.
Admitted.

Lemma is_Rbar_mult_sym (x y z : Rbar) : is_Rbar_mult x y z -> is_Rbar_mult y x z.
Proof.
case: x => [x | | ] ; case: y => [y | | ] ; case: z => [z | | ] //= ; unfold is_Rbar_mult, Rbar_mult' ; try (case: Rle_dec => // H) ; try (case: Rle_lt_or_eq_dec => // H0) ; try (case => <-) ; try (move => _).
Admitted.

Lemma Rbar_mult_comm (x y : Rbar) : Rbar_mult x y = Rbar_mult y x.
Proof.
unfold Rbar_mult.
by rewrite Rbar_mult'_comm.
