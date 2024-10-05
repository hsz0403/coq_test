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

Lemma rep_cons_eq x A U : ~ x el U -> rep (x::A) U = rep A U.
Proof.
intros D.
apply filter_pq_eq.
intros y E.
apply Dec_reflect_eq.
split.
-
intros [<-|F]; tauto.
-
auto.
