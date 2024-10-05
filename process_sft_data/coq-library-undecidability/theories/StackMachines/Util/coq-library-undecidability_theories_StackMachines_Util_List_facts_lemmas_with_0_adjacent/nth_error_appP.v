Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma nth_error_appP {X: Type} {l1 l2: list X} {i: nat} {x: X} : nth_error (l1 ++ l2) i = Some x <-> ((i < length l1 /\ nth_error l1 i = Some x) \/ (length l1 <= i /\ nth_error l2 (i - length l1) = Some x)).
Proof.
constructor.
-
have [Hi | Hi]: i < length l1 \/ length l1 <= i by lia.
+
by rewrite nth_error_app1; firstorder done.
+
by rewrite nth_error_app2; firstorder done.
-
move=> [[? ?]|[? ?]]; by [rewrite nth_error_app1 | rewrite nth_error_app2].
