Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma nth_error_combine_SomeP {X: Type} {i} {x: X} {L: list X} : nth_error L i = Some x <-> nth_error (combine (seq 0 (length L)) L) i = Some (i, x).
Proof.
suff: forall j, nth_error L i = Some x <-> nth_error (combine (seq j (length L)) L) i = Some (j+i, x) by move /(_ 0).
elim: L i; first by case.
move=> y L IH [|i] j /=.
-
have ->: j + 0 = j by lia.
by constructor; move=> [->].
-
have ->: j + S i = S j + i by lia.
by apply: IH.
