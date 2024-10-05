Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma nth_error_Some_In_combineP {X: Type} {i} {x: X} {L: list X} : nth_error L i = Some x <-> In (i, x) (combine (seq 0 (length L)) L).
Proof.
suff: forall j, nth_error L i = Some x <-> In (j+i, x) (combine (seq j (length L)) L) by move /(_ 0).
elim: L i.
{
by move=> [|i] j.
}
move=> y L IH [|i] j /=.
-
constructor.
+
move=> [->].
left.
f_equal.
by lia.
+
case; first by move=> [_ ->].
move /(@in_combine_l nat X).
rewrite in_seq.
by lia.
-
rewrite (IH i (S j)).
have ->: S j + i = j + S i by lia.
constructor.
+
move=> ?.
by right.
+
by case; [move=> []; lia |].
