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

Lemma Rabs_le_between_min_max : forall x y z, Rmin x y <= z <= Rmax x y -> Rabs (z - y) <= Rabs (x - y).
Proof.
intros x y z H.
case (Rle_or_lt x y); intros H'.
rewrite Rmin_left in H;[idtac|exact H'].
rewrite Rmax_right in H;[idtac|exact H'].
rewrite Rabs_left1.
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
apply H.
apply Rle_minus; exact H'.
apply Rle_minus; apply H.
rewrite Rmin_right in H;[idtac|left; exact H'].
rewrite Rmax_left in H;[idtac|left; exact H'].
rewrite Rabs_right.
rewrite Rabs_right.
apply Rplus_le_compat_r.
apply H.
apply Rge_minus; left; apply H'.
apply Rge_minus, Rle_ge; apply H.
