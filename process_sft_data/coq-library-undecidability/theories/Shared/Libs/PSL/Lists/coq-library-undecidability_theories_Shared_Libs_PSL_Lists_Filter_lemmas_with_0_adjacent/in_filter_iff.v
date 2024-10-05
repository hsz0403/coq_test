From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma in_filter_iff x p A : x el filter p A <-> x el A /\ p x.
Proof.
induction A as [|y A]; cbn.
-
tauto.
-
destruct (p y) eqn:E; cbn; rewrite IHA; intuition; subst; auto.
destruct (p x); auto.
