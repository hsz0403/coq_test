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

Lemma RiemannInt_minus : forall (f g : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b) (pr : Riemann_integrable (fun x => f x - g x) a b), RiemannInt pr = RiemannInt pr_f - RiemannInt pr_g.
Proof.
intros.
rewrite <- (Rmult_1_l (RiemannInt pr_g)).
unfold Rminus.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite -(RiemannInt_P13 pr_f pr_g (RiemannInt_P10 (-1) pr_f pr_g)).
apply RiemannInt_ext.
intros ; ring.
