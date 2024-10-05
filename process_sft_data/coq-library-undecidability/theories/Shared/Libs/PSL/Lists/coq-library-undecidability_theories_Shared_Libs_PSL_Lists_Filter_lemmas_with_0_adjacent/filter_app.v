From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_app p A B : filter p (A ++ B) = filter p A ++ filter p B.
Proof.
induction A as [|y A]; cbn.
-
reflexivity.
-
rewrite IHA.
destruct (p y); reflexivity.
