Require Import List.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma In_appr {X : Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof.
move=> ?.
apply: in_or_app.
by right.
