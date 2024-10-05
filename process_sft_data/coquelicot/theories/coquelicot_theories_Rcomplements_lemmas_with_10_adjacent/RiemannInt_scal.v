Ltac evar_last := match goal with | |- ?f ?x => let tx := type of x in let tx := eval simpl in tx in let tmp := fresh "tmp" in evar (tmp : tx) ; refine (@eq_ind tx tmp f _ x _) ; unfold tmp ; clear tmp end.
Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Module MyNat.
End MyNat.
Require Import Even Div2.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Open Scope R_scope.
Definition floor x := proj1_sig (floor_ex x).
Definition floor1 x := proj1_sig (floor1_ex x).
Definition nfloor x pr := proj1_sig (nfloor_ex x pr).
Definition nfloor1 x pr := proj1_sig (nfloor1_ex x pr).
Fixpoint pow2 (n : nat) : nat := match n with | O => 1%nat | S n => (2 * pow2 n)%nat end.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).
Definition sign (x : R) := match total_order_T 0 x with | inleft (left _) => 1 | inleft (right _) => 0 | inright _ => -1 end.
Definition belast {T : Type} (s : seq T) := match s with | [::] => [::] | h :: s => belast h s end.

Lemma RiemannInt_ext : forall (f g : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b) (Heq : forall x, Rmin a b <= x <= Rmax a b -> f x = g x), RiemannInt pr_f = RiemannInt pr_g.
Proof.
intros.
destruct (Rle_lt_dec a b).
apply RiemannInt_P18.
apply r.
intros.
apply Heq.
split.
rewrite (Rmin_left _ _ r).
apply Rlt_le ; apply H.
rewrite (Rmax_right _ _ r).
apply Rlt_le ; apply H.
rewrite (RiemannInt_P8 pr_f (RiemannInt_P1 pr_f)).
rewrite (RiemannInt_P8 pr_g (RiemannInt_P1 pr_g)).
apply Ropp_eq_compat.
apply RiemannInt_P18.
apply Rlt_le ; apply r.
intros.
apply Heq.
split.
rewrite (Rmin_right _ _ (Rlt_le _ _ r)).
apply Rlt_le ; apply H.
rewrite (Rmax_left _ _ (Rlt_le _ _ r)).
Admitted.

Lemma Riemann_integrable_const : forall (c a b : R), Riemann_integrable (fun x => c) a b.
Proof.
intros.
Admitted.

Lemma RiemannInt_const : forall (c a b : R) (pr : Riemann_integrable (fun x => c) a b), RiemannInt pr = c * (b-a).
Proof.
intros.
Admitted.

Lemma Riemann_integrable_plus : forall (f g : R -> R) (a b : R), Riemann_integrable f a b -> Riemann_integrable g a b -> Riemann_integrable (fun x => f x + g x) a b.
Proof.
intros f g a b pr_f pr_g.
apply (Riemann_integrable_ext (fun x => f x + 1 * g x)).
intros ; ring.
Admitted.

Lemma RiemannInt_plus : forall (f g : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b) (pr : Riemann_integrable (fun x => f x + g x) a b), RiemannInt pr = RiemannInt pr_f + RiemannInt pr_g.
Proof.
intros.
rewrite <- (Rmult_1_l (RiemannInt pr_g)).
rewrite <- (RiemannInt_P13 pr_f pr_g (RiemannInt_P10 1 pr_f pr_g)).
apply RiemannInt_ext.
Admitted.

Lemma Riemann_integrable_minus : forall (f g : R -> R) (a b : R), Riemann_integrable f a b -> Riemann_integrable g a b -> Riemann_integrable (fun x => f x - g x) a b.
Proof.
intros f g a b pr_f pr_g.
apply (Riemann_integrable_ext (fun x => f x + (-1) * g x)).
intros ; ring.
Admitted.

Lemma RiemannInt_minus : forall (f g : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b) (pr : Riemann_integrable (fun x => f x - g x) a b), RiemannInt pr = RiemannInt pr_f - RiemannInt pr_g.
Proof.
intros.
rewrite <- (Rmult_1_l (RiemannInt pr_g)).
unfold Rminus.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite -(RiemannInt_P13 pr_f pr_g (RiemannInt_P10 (-1) pr_f pr_g)).
apply RiemannInt_ext.
Admitted.

Lemma Riemann_integrable_opp : forall (f : R -> R) (a b : R), Riemann_integrable f a b -> Riemann_integrable (fun x => - f x) a b.
Proof.
intros f a b pr_f.
apply (Riemann_integrable_ext (fun x => 0 + (-1) * f x)).
intros ; ring.
Admitted.

Lemma RiemannInt_opp : forall (f : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr : Riemann_integrable (fun x => - f x) a b), RiemannInt pr = - RiemannInt pr_f.
Proof.
intros.
rewrite <- (Rmult_1_l (RiemannInt pr_f)).
rewrite <- Ropp_mult_distr_l_reverse.
rewrite -(Rplus_0_l (-1 * RiemannInt pr_f)).
assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
rewrite RiemannInt_const.
ring.
rewrite H ; clear H.
rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (-1) (Riemann_integrable_const 0 a b) pr_f)).
apply RiemannInt_ext.
Admitted.

Lemma Riemann_integrable_scal : forall (f : R -> R) (a b c : R), Riemann_integrable f a b -> Riemann_integrable (fun x => c * f x) a b.
Proof.
intros f a b c pr_f.
apply (Riemann_integrable_ext (fun x => 0 + c * f x)).
intros ; ring.
Admitted.

Lemma ln_pow x n : 0 < x -> ln (x^n) = INR n * ln x.
intro Hx ; induction n as [ | n IH].
rewrite pow_O ln_1 ; simpl ; ring.
rewrite S_INR ; simpl ; rewrite ln_mult ; try intuition.
Admitted.

Lemma ln_le x y : 0 < x -> x <= y -> ln x <= ln y.
Proof.
intros Hx Hxy ; destruct Hxy.
left ; apply ln_increasing.
exact Hx.
exact H.
Admitted.

Lemma ln_div x y : 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof.
intros Hx Hy ; unfold Rdiv.
rewrite ln_mult.
rewrite ln_Rinv.
ring.
exact Hy.
exact Hx.
Admitted.

Lemma derivable_pt_lim_atan : forall x, derivable_pt_lim atan x (/(1 + x^2)).
Proof.
intros x.
apply derive_pt_eq_1 with (derivable_pt_atan x).
replace (x ^ 2) with (x * x) by ring.
rewrite -(Rmult_1_l (Rinv _)).
Admitted.

Lemma RiemannInt_scal : forall (f : R -> R) (a b c : R) (pr_f : Riemann_integrable f a b) (pr : Riemann_integrable (fun x => c * f x) a b), RiemannInt pr = c * RiemannInt pr_f.
Proof.
intros.
rewrite <- (Rplus_0_l (c * RiemannInt pr_f)).
assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
rewrite RiemannInt_const.
ring.
rewrite H ; clear H.
rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (c) (Riemann_integrable_const 0 a b) pr_f)).
apply RiemannInt_ext.
intros ; ring.
