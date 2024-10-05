Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma filter_app p A B : filter p (A ++ B) = filter p A ++ filter p B.
Proof.
induction A as [|y A]; cbn.
-
reflexivity.
-
rewrite IHA.
destruct (p y); reflexivity.
