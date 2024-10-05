Require Import List.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma repeat_appP {X: Type} {x: X} {n m: nat} : repeat x n ++ repeat x m = repeat x (n+m).
Proof.
by elim: n; [| move=> ? /= ->].
