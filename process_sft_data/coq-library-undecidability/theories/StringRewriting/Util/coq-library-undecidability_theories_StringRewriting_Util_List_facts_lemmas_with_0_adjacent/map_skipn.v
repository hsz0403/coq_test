Require Import List.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma map_skipn {X Y: Type} {f: X -> Y} {n} {l} : map f (skipn n l) = skipn n (map f l).
Proof.
elim: n l; first done.
move=> n IH [|? ?]; [done | by apply: IH].
