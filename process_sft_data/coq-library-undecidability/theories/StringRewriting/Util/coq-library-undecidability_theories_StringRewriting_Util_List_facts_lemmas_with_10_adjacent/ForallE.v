Require Import List.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma Forall_repeatI {X : Type} {P : X -> Prop} {x n} : P x -> Forall P (repeat x n).
Proof.
elim: n; first by constructor.
move=> ? IH ?.
Admitted.

Lemma repeat_appP {X: Type} {x: X} {n m: nat} : repeat x n ++ repeat x m = repeat x (n+m).
Proof.
Admitted.

Lemma In_appl {X : Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof.
move=> ?.
apply: in_or_app.
Admitted.

Lemma In_appr {X : Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof.
move=> ?.
apply: in_or_app.
Admitted.

Lemma map_firstn {X Y: Type} {f: X -> Y} {n} {l} : map f (firstn n l) = firstn n (map f l).
Proof.
elim: n l; first done.
move=> n IH [|? ?]; first done.
move=> /=.
congr cons.
Admitted.

Lemma map_skipn {X Y: Type} {f: X -> Y} {n} {l} : map f (skipn n l) = skipn n (map f l).
Proof.
elim: n l; first done.
Admitted.

Lemma ForallE {X : Type} {P : X -> Prop} {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof.
by case.
