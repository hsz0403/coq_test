From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_map X Y p (f: X -> Y) A : filter p (map f A) = map f (filter (fun x => p (f x)) A).
Proof.
induction A;cbn.
reflexivity.
destruct _;cbn; congruence.
