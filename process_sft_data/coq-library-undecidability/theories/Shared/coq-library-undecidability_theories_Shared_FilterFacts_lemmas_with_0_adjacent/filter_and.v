Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma filter_and p q A : filter p (filter q A) = filter (fun x => andb (p x) (q x)) A.
Proof.
induction A as [|x A]; cbn.
reflexivity.
destruct (p x) eqn:E, (q x); cbn; try rewrite E; now rewrite IHA.
