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

Lemma Rbar_mult_correct (x y : Rbar) : ex_Rbar_mult x y -> is_Rbar_mult x y (Rbar_mult x y).
Proof.
Admitted.

Lemma Rbar_mult_correct' (x y z : Rbar) : is_Rbar_mult x y z -> ex_Rbar_mult x y.
Proof.
unfold is_Rbar_mult ; case: x => [x | | ] ; case: y => [y | | ] //= ; case: Rle_dec => //= H ; try (case: Rle_lt_or_eq_dec => //=) ; intros.
by apply Rgt_not_eq.
by apply Rlt_not_eq, Rnot_le_lt.
by apply Rgt_not_eq.
by apply Rlt_not_eq, Rnot_le_lt.
by apply Rgt_not_eq.
by apply Rlt_not_eq, Rnot_le_lt.
by apply Rgt_not_eq.
Admitted.

Lemma Rbar_finite_eq (x y : R) : Finite x = Finite y <-> x = y.
Proof.
split ; intros.
apply Rle_antisym ; apply Rnot_lt_le ; intro.
assert (Rbar_lt (Finite y) (Finite x)).
simpl ; apply H0.
rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
assert (Rbar_lt (Finite x) (Finite y)).
simpl ; apply H0.
rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
Admitted.

Lemma Rbar_finite_neq (x y : R) : Finite x <> Finite y <-> x <> y.
Proof.
Admitted.

Lemma Rbar_lt_not_eq (x y : Rbar) : Rbar_lt x y -> x<>y.
Proof.
destruct x ; destruct y ; simpl ; try easy.
intros H H0.
Admitted.

Lemma Rbar_not_le_lt (x y : Rbar) : ~ Rbar_le x y -> Rbar_lt y x.
Proof.
Admitted.

Lemma Rbar_lt_not_le (x y : Rbar) : Rbar_lt y x -> ~ Rbar_le x y.
Proof.
destruct x ; destruct y ; simpl ; intuition.
apply (Rlt_irrefl r0).
Admitted.

Lemma Rbar_not_lt_le (x y : Rbar) : ~ Rbar_lt x y -> Rbar_le y x.
Proof.
destruct x ; destruct y ; simpl ; intuition.
Admitted.

Lemma Rbar_le_not_lt (x y : Rbar) : Rbar_le y x -> ~ Rbar_lt x y.
Proof.
destruct x ; destruct y ; simpl ; intuition ; contradict H0.
Admitted.

Lemma Rbar_le_refl : forall x : Rbar, Rbar_le x x.
Proof.
intros [x| |] ; try easy.
Admitted.

Lemma Rbar_total_order (x y : Rbar) : {Rbar_lt x y} + {x = y} + {Rbar_lt y x}.
Proof.
destruct x ; destruct y ; simpl ; intuition.
Admitted.

Lemma Rbar_eq_dec (x y : Rbar) : {x = y} + {x <> y}.
Proof.
intros ; destruct (Rbar_total_order x y) as [[H|H]|H].
right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ; try easy.
contradict H.
apply Rbar_finite_eq in H ; try apply Rle_not_lt, Req_le ; auto.
left ; apply H.
right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ; try easy.
contradict H.
Admitted.

Lemma Rbar_lt_dec (x y : Rbar) : {Rbar_lt x y} + {~Rbar_lt x y}.
Proof.
destruct (Rbar_total_order x y) as [H|H] ; [ destruct H as [H|H]|].
now left.
right ; rewrite H ; clear H ; destruct y ; auto ; apply Rlt_irrefl ; auto.
Admitted.

Lemma Rbar_lt_le_dec (x y : Rbar) : {Rbar_lt x y} + {Rbar_le y x}.
Proof.
destruct (Rbar_total_order x y) as [[H|H]|H].
now left.
right.
rewrite H.
apply Rbar_le_refl.
right.
Admitted.

Lemma Rbar_le_dec (x y : Rbar) : {Rbar_le x y} + {~Rbar_le x y}.
Proof.
destruct (Rbar_total_order x y) as [[H|H]|H].
left.
now apply Rbar_lt_le.
left.
rewrite H.
apply Rbar_le_refl.
right.
Admitted.

Lemma Rbar_le_lt_dec (x y : Rbar) : {Rbar_le x y} + {Rbar_lt y x}.
Proof.
destruct (Rbar_total_order x y) as [[H|H]|H].
left.
now apply Rbar_lt_le.
left.
rewrite H.
apply Rbar_le_refl.
Admitted.

Lemma Rbar_le_lt_or_eq_dec (x y : Rbar) : Rbar_le x y -> { Rbar_lt x y } + { x = y }.
Proof.
destruct (Rbar_total_order x y) as [[H|H]|H].
now left.
now right.
intros K.
Admitted.

Lemma Rbar_lt_trans (x y z : Rbar) : Rbar_lt x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
destruct x ; destruct y ; destruct z ; simpl ; intuition.
Admitted.

Lemma Rbar_lt_le_trans (x y z : Rbar) : Rbar_lt x y -> Rbar_le y z -> Rbar_lt x z.
Proof.
destruct x ; destruct y ; destruct z ; simpl ; intuition.
Admitted.

Lemma Rbar_le_lt_trans (x y z : Rbar) : Rbar_le x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
destruct x ; destruct y ; destruct z ; simpl ; intuition.
Admitted.

Lemma Rbar_lt_le : forall x y : Rbar, Rbar_lt x y -> Rbar_le x y.
Proof.
intros [x| |] [y| |] ; try easy.
apply Rlt_le.
