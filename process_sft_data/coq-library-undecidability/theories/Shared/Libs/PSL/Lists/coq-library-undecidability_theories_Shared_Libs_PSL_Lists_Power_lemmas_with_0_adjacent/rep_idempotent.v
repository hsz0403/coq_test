From Undecidability.Shared.Libs.PSL Require Import BaseLists Dupfree.
Section Power.
Variable X : Type.
Fixpoint power (U: list X ) : list (list X) := match U with | nil => [nil] | x :: U' => power U' ++ map (cons x) (power U') end.
End Power.
Section PowerRep.
Variable X : eqType.
Implicit Types A U : list X.
Definition rep (A U : list X) : list X := filter (fun x => Dec (x el A)) U.
End PowerRep.

Lemma rep_idempotent A U : rep (rep A U) U = rep A U.
Proof.
unfold rep at 1 3.
apply filter_pq_eq.
intros x D.
apply Dec_reflect_eq.
split.
+
apply rep_incl.
+
intros E.
apply in_filter_iff.
auto.
