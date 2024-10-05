Require Import List.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma Forall_repeatI {X : Type} {P : X -> Prop} {x n} : P x -> Forall P (repeat x n).
Proof.
elim: n; first by constructor.
move=> ? IH ?.
constructor; [done | by apply: IH].
