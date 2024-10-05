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

Lemma fp : F C = C.
Proof.
pose (size (A : list X) := card R - card A).
replace C with (it F (size nil) nil).
-
apply it_fp.
intros n.
cbn.
set (J:= it F n nil).
unfold FP, F.
destruct (pick J) as [[x B]|B].
+
right.
assert (G: card J < card (x :: J)).
{
apply card_lt with (x:=x); intuition.
}
assert (H: card (x :: J) <= card R).
{
apply card_le, incl_cons.
apply B.
apply it_incl.
}
unfold size.
lia.
+
auto.
-
unfold C, size.
f_equal.
change (card nil) with 0.
lia.
