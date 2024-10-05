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

Lemma rep_eq' A B U : (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.
Proof.
intros D.
apply filter_pq_eq.
intros x E.
apply Dec_reflect_eq.
auto.
