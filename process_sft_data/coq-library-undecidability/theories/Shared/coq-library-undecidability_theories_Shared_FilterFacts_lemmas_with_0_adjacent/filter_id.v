Require Import List.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
Local Notation "x 'el' L" := (In x L) (at level 50).
Local Notation "A '<<=' B" := (incl A B) (at level 50).
End Filter.

Lemma filter_id p A : (forall x, x el A -> p x = true) -> filter p A = A.
Proof.
intros D.
induction A as [|x A]; cbn.
-
reflexivity.
-
destruct (p x) eqn:E.
+
f_equal.
eapply IHA.
intros y H.
apply D.
cbn.
eauto.
+
exfalso.
rewrite D in E.
congruence.
cbn.
eauto.
