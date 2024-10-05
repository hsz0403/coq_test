Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma filter_pq_eq p q A : (forall x, x el A -> p x = q x) -> filter p A = filter q A.
Proof.
intros C; induction A as [|x A]; cbn.
-
reflexivity.
-
destruct (p x) eqn:D, (q x) eqn:E.
+
f_equal.
eapply IHA.
intros.
eapply C.
cbn.
eauto.
+
exfalso.
enough (p x = q x) by congruence.
firstorder.
+
exfalso.
enough (p x = q x) by congruence.
firstorder.
+
firstorder.
