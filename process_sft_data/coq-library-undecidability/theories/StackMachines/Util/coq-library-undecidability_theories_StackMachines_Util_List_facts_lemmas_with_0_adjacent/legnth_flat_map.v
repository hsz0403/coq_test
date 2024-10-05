Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma legnth_flat_map {X Y: Type} {f: X -> list Y} {l: list X} {n: nat}: (forall x, length (f x) <= n) -> length (flat_map f l) <= n * length l.
Proof.
move=> Hf.
elim: l.
-
move=> * /=.
by lia.
-
move=> x l IH /=.
rewrite app_length.
have := Hf x.
by lia.
