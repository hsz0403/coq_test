Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma repeat_appP {X: Type} {x: X} {n m: nat} : repeat x n ++ repeat x m = repeat x (n+m).
Proof.
by elim: n; [| move=> ? /= ->].
