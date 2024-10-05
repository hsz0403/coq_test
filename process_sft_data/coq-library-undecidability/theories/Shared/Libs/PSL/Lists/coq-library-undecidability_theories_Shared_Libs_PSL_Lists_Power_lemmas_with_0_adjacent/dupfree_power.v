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

Lemma dupfree_power U : dupfree U -> dupfree (power U).
Proof.
intros D.
induction D as [|x U E D]; cbn.
-
constructor.
now auto.
constructor.
-
apply dupfree_app.
+
intros [A [F G]].
apply in_map_iff in G as [A' [G G']].
subst A.
apply E.
apply (power_incl F).
auto.
+
exact IHD.
+
apply dupfree_map; congruence.
