Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma in_split_informative {X: Type} {x: X} {l: list X} : (forall (x y: X), {x = y} + {x <> y}) -> In x l -> { '(l1, l2) | l = l1 ++ x :: l2 }.
Proof.
move=> H_dec.
elim: l; first done.
move=> y l IH /=.
case: (H_dec y x).
-
move=> <- _.
by exists ([], l).
-
move=> ? Hxl.
have : In x l by case: Hxl.
move /IH => [[l1 l2] ->].
by exists (y :: l1, l2).
