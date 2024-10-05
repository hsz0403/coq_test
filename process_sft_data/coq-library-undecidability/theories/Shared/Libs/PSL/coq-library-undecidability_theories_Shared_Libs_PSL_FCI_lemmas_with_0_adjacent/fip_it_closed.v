From Undecidability.Shared.Libs.PSL Require Import Lists.Cardinality Numbers.
Section Fip.
Variables (X: eqType) (sigma: list X -> X -> bool) (R: list X).
Inductive fip : X -> Prop := | fip_intro A x : (forall x, x el A -> fip x) -> sigma A x -> x el R -> fip x.
Definition fip_monotone := forall A B x, A <<= B -> sigma A x -> sigma B x.
Definition fip_closed A := forall x, x el R -> sigma A x -> x el A.
Fixpoint fip_it n A : list X := match n, find (fun x => Dec (~ x el A /\ sigma A x)) R with | S n', Some x => fip_it n' (x::A) | _, _ => A end.
End Fip.
Module FCI.
Section FCI.
Variables (X: eqType) (sigma: list X -> X -> bool) (R: list X).
Definition F (A : list X) : list X.
Proof.
destruct (pick A) as [[x _]|_].
-
exact (x::A).
-
exact A.
Defined.
Definition C := it F (card R) nil.
End FCI.
End FCI.

Lemma fip_it_closed n A : A <<= R -> card R <= n + card A -> fip_closed (fip_it n A).
Proof.
revert A.
induction n as [|n IH]; cbn; intros A H H1.
-
enough (A === R) as (H2&H3) by (hnf; auto).
apply card_or in H as [H|H].
exact H.
lia.
-
destruct (find _ R) eqn:E.
+
apply find_some in E as [H2 (H3&H4) % Dec_true].
apply IH.
now auto.
rewrite card_cons'.
lia.
auto.
+
intros x H2 H3.
apply dec_DN.
now auto.
apply find_none with (x := x) in E; auto.
apply Dec_false in E; auto.
