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

Lemma sign_min_max (a b : R) : sign (b - a) * (Rmax a b - Rmin a b) = b - a.
Proof.
unfold sign.
case total_order_T as [[H|H]|H].
assert (K := proj2 (Rminus_le_0 a b) (Rlt_le _ _ H)).
rewrite (Rmax_right _ _ K) (Rmin_left _ _ K).
apply Rmult_1_l.
rewrite -H.
apply Rmult_0_l.
assert (K : b <= a).
apply Rnot_lt_le.
contradict H.
apply Rle_not_lt.
apply -> Rminus_le_0.
now apply Rlt_le.
rewrite (Rmax_left _ _ K) (Rmin_right _ _ K).
ring.
