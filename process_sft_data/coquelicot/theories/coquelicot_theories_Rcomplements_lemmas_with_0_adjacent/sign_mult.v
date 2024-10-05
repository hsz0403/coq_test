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

Lemma sign_mult (x y : R) : sign (x * y) = sign x * sign y.
Proof.
wlog: x / (0 < x) => [Hw | Hx].
case: (Rle_lt_dec 0 x) => Hx.
case: Hx => Hx.
by apply Hw.
rewrite -Hx Rmult_0_l.
rewrite sign_0.
by rewrite Rmult_0_l.
rewrite -(Ropp_involutive x).
rewrite sign_opp Ropp_mult_distr_l_reverse sign_opp Hw.
ring.
by apply Ropp_0_gt_lt_contravar.
wlog: y / (0 < y) => [Hw | Hy].
case: (Rle_lt_dec 0 y) => Hy.
case: Hy => Hy.
by apply Hw.
rewrite -Hy Rmult_0_r.
rewrite sign_0.
by rewrite Rmult_0_r.
rewrite -(Ropp_involutive y).
rewrite sign_opp Ropp_mult_distr_r_reverse sign_opp Hw.
ring.
by apply Ropp_0_gt_lt_contravar.
have Hxy : 0 < x * y.
by apply Rmult_lt_0_compat.
rewrite -> 3!sign_eq_1 by easy.
by rewrite Rmult_1_l.
