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
apply Rlt_le ; apply H.
