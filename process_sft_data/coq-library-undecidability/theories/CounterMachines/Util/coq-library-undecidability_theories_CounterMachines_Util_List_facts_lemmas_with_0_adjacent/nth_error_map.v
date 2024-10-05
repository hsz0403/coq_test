Require Import List.
Import ListNotations.
Require Import Arith Lia.
Require Import ssreflect ssrbool ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Section ForallNorm.
Variable T : Type.
Variable P : T -> Prop.
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).
End ForallNorm.

Lemma nth_error_map {X Y: Type} {f: X -> Y} {l: list X} {n: nat} : nth_error (map f l) n = omap f (nth_error l n).
Proof.
elim: n l; first by case.
move=> n IH.
case; first done.
move=> x l /=.
by rewrite /nth_error -?/(nth_error _ _).
