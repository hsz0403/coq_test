Require Import List.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma ForallE {X : Type} {P : X -> Prop} {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof.
by case.
