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

Lemma interval_finite_subdiv_between (a b : R) (eps : posreal) (Hab : a <= b) : let l := proj1_sig (interval_finite_subdiv a b eps Hab) in forall i, (i < size l)%nat -> a <= nth 0 l i <= b.
Proof.
case: interval_finite_subdiv => l Hl /= i Hi.
case: Hl => <- ; case => <- Hl.
move: (fun i Hi => proj1 (Hl i Hi)) => {Hl} Hl.
rewrite -nth0 (last_nth 0).
suff : forall n m, (n <= m)%nat -> (m < size l)%nat -> nth 0 l n <= nth 0 l m.
move => {Hl} Hl ; split.
apply Hl ; by intuition.
case: l Hi Hl => /= [ | x0 l] Hi Hl.
by apply lt_n_O in Hi.
apply Hl ; by intuition.
elim: l Hl {i Hi} => [ | x0 l IH] Hl n m Hnm Hm.
by apply lt_n_O in Hm.
case: n m Hnm Hm => [ | n] m //= Hnm Hm.
clear Hnm ; elim: m Hm => {IH} /= [ | m IH] Hm.
by apply Rle_refl.
apply Rle_trans with (nth 0 (x0 :: l) m).
apply IH ; intuition.
by apply Rlt_le, Hl.
case: m Hnm Hm => /= [ | m] Hnm Hm.
by apply le_Sn_O in Hnm.
apply IH ; try by intuition.
move => i Hi.
apply (Hl (S i)).
by apply lt_n_S.
