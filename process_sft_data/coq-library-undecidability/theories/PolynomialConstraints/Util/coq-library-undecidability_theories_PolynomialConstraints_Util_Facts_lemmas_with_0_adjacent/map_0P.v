Require Import List.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma map_0P {X: Type} {A: list X} : (map (fun=> 0) A) = repeat 0 (length A).
Proof.
elim: A; [done | by move=> > /= ->].
