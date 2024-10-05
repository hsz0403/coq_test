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

Lemma Rle_pow_lin (a : R) (n : nat) : 0 <= a -> 1 + INR n * a <= (1 + a) ^ n.
Proof.
intro Ha.
induction n.
apply Req_le ; simpl ; ring.
rewrite S_INR.
replace (1 + (INR n + 1) * a) with ((1 + INR n * a) + a) by ring.
apply Rle_trans with ((1 + a) ^ n + a).
apply Rplus_le_compat_r.
exact IHn.
replace ((1+a)^(S n)) with ((1+a)^n + a * (1+a)^n) by (simpl ; ring).
apply Rplus_le_compat_l.
pattern a at 1.
rewrite <- (Rmult_1_r a).
apply Rmult_le_compat_l.
exact Ha.
clear IHn.
apply pow_R1_Rle.
pattern 1 at 1.
rewrite <- (Rplus_0_r 1).
apply Rplus_le_compat_l.
exact Ha.
