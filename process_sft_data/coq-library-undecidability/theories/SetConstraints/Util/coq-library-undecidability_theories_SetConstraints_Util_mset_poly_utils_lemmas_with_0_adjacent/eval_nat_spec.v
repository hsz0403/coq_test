Require Import PeanoNat Lia List.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC.
From Undecidability.SetConstraints.Util Require Import Facts mset_eq_utils.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Definition eval p A := fold_right plus 0 (map (fun n => Nat.pow p n) A).
Definition eval_norm := (@eval_appP, @eval_singletonP, @eval_consP).

Lemma eval_nat_spec {p q A} : p < q -> eval p A = eval q A -> Forall (fun a => 0 = a) A.
Proof.
move /eval_monotone => /(_ A).
case; [by lia | done].
