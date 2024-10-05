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

Lemma sum_f_R0_skip (u : nat -> R) (n : nat) : sum_f_R0 (fun k => u (n - k)%nat) n = sum_f_R0 u n.
Proof.
suff H : forall n m, (n < m)%nat -> sum_f n m (fun k => u ((m - k) + n)%nat) = sum_f n m u.
case: n => [ | n] //.
move: (H _ _ (lt_O_Sn n)) => {H} H.
rewrite /sum_f in H.
transitivity (sum_f_R0 (fun x : nat => u (S n - (x + 0) + 0)%nat) (S n - 0)).
replace (S n - 0)%nat with (S n) by auto.
elim: {2 4}(S n) => [ | m IH] //.
simpl ; by rewrite plus_0_r.
rewrite /sum_f_R0 -/sum_f_R0 -IH.
apply f_equal.
by rewrite ?plus_0_r.
rewrite H.
replace (S n - 0)%nat with (S n) by auto.
elim: (S n) => [ | m IH] //.
rewrite /sum_f_R0 -/sum_f_R0 -IH.
apply f_equal.
by rewrite plus_0_r.
move => {n} n m H.
elim: m u H => [ | m IH] u H //.
apply lt_n_Sm_le, le_lt_eq_dec in H ; case: H IH => [H IH | -> _ {n}] //.
rewrite sum_f_n_Sm ; try by intuition.
replace (sum_f n (S m) u) with (sum_f n (S m) u - u n + u n) by ring.
rewrite -sum_f_Sn_m ; try by intuition.
rewrite sum_f_u_Sk ; try by intuition.
rewrite -(IH (fun k => u (S k))) => {IH} ; try by intuition.
apply f_equal2.
rewrite /sum_f.
elim: {1 3 4}(m - n)%nat (le_refl (m-n)%nat) => [ | k IH] // Hk ; rewrite /sum_f_R0 -/sum_f_R0.
apply f_equal.
rewrite plus_0_l MyNat.sub_add ; intuition.
rewrite IH ; try by intuition.
by rewrite minus_diag plus_0_l.
rewrite /sum_f.
rewrite -minus_Sn_m ; try by intuition.
rewrite minus_diag.
rewrite /sum_f_R0 -/sum_f_R0.
replace (1+m)%nat with (S m) by ring.
rewrite plus_0_l minus_diag MyNat.sub_add ; intuition.
