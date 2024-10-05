From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_and p q A : filter p (filter q A) = filter (fun x => p x && q x) A.
Proof.
induction A as [|x A]; cbn.
reflexivity.
destruct (p x) eqn:E, (q x); cbn; try rewrite E; now rewrite IHA.
