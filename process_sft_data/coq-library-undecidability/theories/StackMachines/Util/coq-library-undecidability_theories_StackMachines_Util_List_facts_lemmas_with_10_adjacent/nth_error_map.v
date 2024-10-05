Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma seq_last {m n} : seq m (1+n) = seq m n ++ [m + n].
Proof.
have -> : 1+n = n+1 by lia.
Admitted.

Lemma nth_error_seq {m l n: nat} : n < l -> nth_error (seq m l) n = Some (m+n).
Proof.
elim: n m l.
-
move=> m [|l]; first by lia.
move=> /= _.
congr Some.
by lia.
-
move=> n IH m [|l /= ?]; first by lia.
Admitted.

Lemma repeat_appP {X: Type} {x: X} {n m: nat} : repeat x n ++ repeat x m = repeat x (n+m).
Proof.
Admitted.

Lemma repeat_app_appP {X: Type} {x: X} {xs: list X} {n m: nat} : repeat x n ++ (repeat x m ++ xs) = repeat x (n+m) ++ xs.
Proof.
Admitted.

Lemma repeat_singP {X: Type} {x: X} : [x] = repeat x 1.
Proof.
Admitted.

Lemma app_assoc' {X: Type} {xs ys zs: list X} : (xs ++ ys) ++ zs = xs ++ ys ++ zs.
Proof.
Admitted.

Lemma cons_repeat_app {X: Type} {x: X} {xs: list X} {m: nat} : x :: (repeat x m ++ xs) = (repeat x (m+1) ++ xs).
Proof.
Admitted.

Lemma app_singP {X: Type} {x: X} {l: list X} : [x] ++ l = x :: l.
Proof.
Admitted.

Lemma app_repeat_cons {X: Type} {n: nat} {x: X} {l: list X} : repeat x (1+n) ++ l = x :: (repeat x n ++ l).
Proof.
Admitted.

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
Admitted.

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
Admitted.

Lemma nth_error_map {X Y: Type} {f: X -> Y} {l: list X} {n: nat} : nth_error (map f l) n = omap f (nth_error l n).
Proof.
elim: n l; first by case.
move=> n IH.
case; first done.
move=> x l /=.
by rewrite /nth_error -?/(nth_error _ _).
