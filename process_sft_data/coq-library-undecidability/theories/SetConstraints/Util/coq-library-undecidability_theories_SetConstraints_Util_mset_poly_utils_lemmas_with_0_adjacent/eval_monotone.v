Require Import PeanoNat Lia List.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC.
From Undecidability.SetConstraints.Util Require Import Facts mset_eq_utils.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Definition eval p A := fold_right plus 0 (map (fun n => Nat.pow p n) A).
Definition eval_norm := (@eval_appP, @eval_singletonP, @eval_consP).

Lemma eval_monotone {p q A} : p < q -> eval p A < eval q A \/ Forall (fun a => 0 = a) A.
Proof.
move=> ?.
elim: A; first by right.
case.
{
move=> A IH.
rewrite ? eval_consP ? Forall_norm => /=.
case: IH=> IH; first by lia.
by right.
}
move=> a A IH.
left.
rewrite ? eval_consP.
have ? := Nat.pow_lt_mono_l p q (S a) ltac:(done) ltac:(done).
case: IH; first by lia.
move /eval_nat => H.
rewrite ? H.
by lia.
