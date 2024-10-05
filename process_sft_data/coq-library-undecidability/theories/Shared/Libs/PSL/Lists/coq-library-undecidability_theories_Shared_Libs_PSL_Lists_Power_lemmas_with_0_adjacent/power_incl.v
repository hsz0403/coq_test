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

Lemma power_incl A U : A el power U -> A <<= U.
Proof.
revert A; induction U as [|x U]; cbn; intros A D.
-
destruct D as [[]|[]]; auto.
-
apply in_app_iff in D as [E|E].
now auto.
apply in_map_iff in E as [A' [E F]].
subst A.
auto.
