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

Lemma fip_least A x : fip_monotone -> fip_closed A -> fip x -> x el A.
Proof.
intros C D.
induction 1 as [B x _ IH F G].
apply (D _ G).
revert F.
apply C.
exact IH.
