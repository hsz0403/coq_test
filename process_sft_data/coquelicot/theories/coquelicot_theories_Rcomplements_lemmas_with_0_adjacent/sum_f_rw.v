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

Lemma sum_f_rw (a : nat -> R) (n m : nat) : (n < m)%nat -> sum_f (S n) m a = sum_f_R0 a m - sum_f_R0 a n.
Proof.
intro Hnm ; unfold sum_f.
revert a n Hnm.
induction m ; intros a n Hnm.
apply lt_n_O in Hnm ; intuition.
rewrite (decomp_sum _ _ (lt_O_Sn _)) ; simpl.
revert Hnm ; destruct n ; intro Hnm.
rewrite <- minus_n_O ; simpl ; ring_simplify.
clear Hnm IHm.
induction m ; simpl.
reflexivity.
rewrite <- plus_n_Sm, plus_0_r, IHm ; reflexivity.
rewrite (decomp_sum _ _ (lt_O_Sn _)) ; simpl ; ring_simplify.
apply lt_S_n in Hnm.
rewrite <- (IHm _ _ Hnm).
clear IHm.
induction (m - S n)%nat ; simpl.
reflexivity.
rewrite <- plus_n_Sm, IHn0 ; reflexivity.
