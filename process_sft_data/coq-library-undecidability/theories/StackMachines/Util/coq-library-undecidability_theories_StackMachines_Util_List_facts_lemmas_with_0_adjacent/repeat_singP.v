Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma repeat_singP {X: Type} {x: X} : [x] = repeat x 1.
Proof.
done.
