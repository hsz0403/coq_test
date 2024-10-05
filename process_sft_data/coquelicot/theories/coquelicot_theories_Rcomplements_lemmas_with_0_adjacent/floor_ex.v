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

Lemma floor_ex : forall x : R, {n : Z | IZR n <= x < IZR n + 1}.
Proof.
intros.
exists (up (x-1)) ; split.
assert (Rw : x = 1 + (x-1)) ; [ring | rewrite {2}Rw => {Rw}].
assert (Rw :IZR (up (x - 1)) = (IZR (up (x - 1)) - (x - 1)) + (x-1)) ; [ring | rewrite Rw ; clear Rw].
apply Rplus_le_compat_r, (proj2 (archimed _)).
assert (Rw : x = (x-1) + 1) ; [ring | rewrite {1}Rw ; clear Rw].
apply Rplus_lt_compat_r, (proj1 (archimed _)).
