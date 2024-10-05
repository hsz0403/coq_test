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

Lemma dupfree_in_power U A : A el power U -> dupfree U -> dupfree A.
Proof.
intros E D.
revert A E.
induction D as [|x U D D']; cbn; intros A E.
-
destruct E as [[]|[]].
constructor.
-
apply in_app_iff in E as [E|E].
+
auto.
+
apply in_map_iff in E as [A' [E E']].
subst A.
constructor.
*
intros F; apply D.
apply (power_incl E'), F.
*
auto.
