Require Import List.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).

Lemma Forall_nil_iff {X: Type} {P: X -> Prop} : Forall P [] <-> True.
Proof.
by constructor.
