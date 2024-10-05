Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma in_filter_iff x p A : x el filter p A <-> x el A /\ p x = true.
Proof.
induction A as [|y A]; cbn.
-
tauto.
-
destruct (p y) eqn:E; cbn; rewrite IHA; intuition; subst; auto.
congruence.
