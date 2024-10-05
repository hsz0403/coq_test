Require Import List.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).

Lemma Forall_cons_iff {T: Type} {P: T -> Prop} {a l} : Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
constructor.
-
move=> H.
by inversion H.
-
move=> [? ?].
by constructor.
