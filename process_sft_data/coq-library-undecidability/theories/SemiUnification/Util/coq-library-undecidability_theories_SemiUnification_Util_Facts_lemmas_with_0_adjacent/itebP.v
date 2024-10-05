Require Import List.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).

Lemma itebP {X: Type} {P: bool -> X} {b: bool} : (if b then P true else P false) = P b.
Proof.
by case: b.
