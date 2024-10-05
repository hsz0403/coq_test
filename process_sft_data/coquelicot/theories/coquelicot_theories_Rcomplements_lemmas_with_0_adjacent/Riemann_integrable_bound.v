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

Lemma Riemann_integrable_bound (f : R -> R) (a b : R) : Riemann_integrable f a b -> exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
move => pr ; case (pr (mkposreal _ Rlt_0_1)) => {pr} phi [psi [pr _]] ; case: (StepFun_bound phi) => M_phi H_phi ; case: (StepFun_bound psi) => M_psi H_psi ; exists (M_psi + M_phi) => x Hx.
apply Rle_trans with (2 := Rplus_le_compat _ _ _ _ (H_psi _ Hx) (H_phi _ Hx)).
have: (f x = (f x - phi x) + phi x) ; first by ring.
move => -> ; apply Rplus_le_compat_r, Rle_trans with (1 := Rle_abs _), pr, Hx.
