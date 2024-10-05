From Undecidability.Shared.Libs.PSL Require Import BaseLists.
Section Filter.
Variable X : Type.
Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
End Filter.

Lemma filter_id p A : (forall x, x el A -> p x) -> filter p A = A.
Proof.
intros D.
induction A as [|x A]; cbn.
-
reflexivity.
-
destruct (p x) eqn:E.
+
f_equal; auto.
+
exfalso.
apply bool_Prop_false in E.
auto.
