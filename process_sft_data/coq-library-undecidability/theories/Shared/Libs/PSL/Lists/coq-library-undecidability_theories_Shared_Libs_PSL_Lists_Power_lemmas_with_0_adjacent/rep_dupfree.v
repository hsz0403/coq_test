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

Lemma rep_dupfree A U : dupfree U -> A el power U -> rep A U = A.
Proof.
intros D; revert A.
induction D as [|x U E F]; intros A G.
-
destruct G as [[]|[]]; reflexivity.
-
cbn in G.
apply in_app_iff in G as [G|G].
+
rewrite rep_cons'.
now auto.
contradict E.
apply (power_incl G), E.
+
apply in_map_iff in G as [A' [<- H]].
specialize (IHF _ H).
rewrite rep_cons.
2:now auto.
rewrite rep_cons_eq.
now rewrite IHF.
exact E.
