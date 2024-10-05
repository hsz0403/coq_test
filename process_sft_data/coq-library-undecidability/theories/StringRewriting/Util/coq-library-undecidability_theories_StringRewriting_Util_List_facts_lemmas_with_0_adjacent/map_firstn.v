Require Import List.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma map_firstn {X Y: Type} {f: X -> Y} {n} {l} : map f (firstn n l) = firstn n (map f l).
Proof.
elim: n l; first done.
move=> n IH [|? ?]; first done.
move=> /=.
congr cons.
by apply: IH.
