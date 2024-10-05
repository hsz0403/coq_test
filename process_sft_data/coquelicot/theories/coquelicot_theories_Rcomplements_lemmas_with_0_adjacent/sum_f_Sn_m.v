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

Lemma sum_f_Sn_m (u : nat -> R) (n m : nat) : (n < m)%nat -> sum_f (S n) m u = sum_f n m u - u n.
Proof.
move => H.
elim: m n H => [ | m IH] // n H.
by apply lt_n_O in H.
rewrite sum_f_u_Sk ; try by intuition.
rewrite sum_f_n_Sm ; try by intuition.
replace (sum_f n m u + u (S m) - u n) with ((sum_f n m u - u n) + u (S m)) by ring.
apply lt_n_Sm_le, le_lt_eq_dec in H.
case: H => [ H | -> {n} ] //.
rewrite -IH => //.
rewrite /sum_f ; simpl.
rewrite MyNat.sub_succ_r.
apply lt_minus_O_lt in H.
rewrite -{3}(MyNat.sub_add n m) ; try by intuition.
case: (m-n)%nat H => {IH} [ | k] //= H.
by apply lt_n_O in H.
apply (f_equal (fun y => y + _)).
elim: k {H} => [ | k IH] //.
rewrite /sum_f_R0 -/sum_f_R0 IH ; repeat apply f_equal ; intuition.
rewrite /sum_f minus_diag /= ; ring.
