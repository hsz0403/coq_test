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

Lemma nfloor1_ex : forall x : R, 0 < x -> {n : nat | INR n < x <= INR n + 1}.
Proof.
intros.
destruct (nfloor_ex x (Rlt_le _ _ H)) as (n,(Hn1,Hn2)).
destruct (Rle_lt_or_eq_dec (INR n) x Hn1).
exists n ; split.
apply r.
apply Rlt_le, Hn2.
destruct n.
contradict H.
rewrite <- e ; simpl ; apply Rlt_irrefl.
exists n ; rewrite <- e ; split.
apply lt_INR, lt_n_Sn.
rewrite <- (S_INR) ; apply Rle_refl.
