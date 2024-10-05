Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma app_singP {X: Type} {x: X} {l: list X} : [x] ++ l = x :: l.
Proof.
done.
