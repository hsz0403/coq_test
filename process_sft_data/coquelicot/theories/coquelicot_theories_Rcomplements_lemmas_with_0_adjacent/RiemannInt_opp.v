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
intros ; ring.
