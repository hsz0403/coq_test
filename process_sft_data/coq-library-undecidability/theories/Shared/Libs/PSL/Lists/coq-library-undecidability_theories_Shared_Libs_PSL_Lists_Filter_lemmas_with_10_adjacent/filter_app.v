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
Admitted.

Lemma filter_incl p A : filter p A <<= A.
Proof.
intros x D.
apply in_filter_iff in D.
Admitted.

Lemma filter_mono p A B : A <<= B -> filter p A <<= filter p B.
Proof.
intros D x E.
apply in_filter_iff in E as [E E'].
apply in_filter_iff.
Admitted.

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
Admitted.

Lemma filter_fst p x A : p x -> filter p (x::A) = x::filter p A.
Proof.
cbn.
Admitted.

Lemma filter_fst' p x A : ~ p x -> filter p (x::A) = filter p A.
Proof.
cbn.
Admitted.

Lemma filter_pq_mono p q A : (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.
Proof.
intros D x E.
apply in_filter_iff in E as [E E'].
apply in_filter_iff.
Admitted.

Lemma filter_pq_eq p q A : (forall x, x el A -> p x = q x) -> filter p A = filter q A.
Proof.
intros C; induction A as [|x A]; cbn.
-
reflexivity.
-
destruct (p x) eqn:D, (q x) eqn:E.
+
f_equal.
auto.
+
exfalso.
enough (p x = q x) by congruence.
auto.
+
exfalso.
enough (p x = q x) by congruence.
auto.
+
Admitted.

Lemma filter_and p q A : filter p (filter q A) = filter (fun x => p x && q x) A.
Proof.
induction A as [|x A]; cbn.
reflexivity.
Admitted.

Lemma filter_comm p q A : filter p (filter q A) = filter q (filter p A).
Proof.
rewrite !filter_and.
apply filter_pq_eq.
intros x _.
Admitted.

Lemma filter_map X Y p (f: X -> Y) A : filter p (map f A) = map f (filter (fun x => p (f x)) A).
Proof.
induction A;cbn.
reflexivity.
Admitted.

Lemma filter_app p A B : filter p (A ++ B) = filter p A ++ filter p B.
Proof.
induction A as [|y A]; cbn.
-
reflexivity.
-
rewrite IHA.
destruct (p y); reflexivity.
