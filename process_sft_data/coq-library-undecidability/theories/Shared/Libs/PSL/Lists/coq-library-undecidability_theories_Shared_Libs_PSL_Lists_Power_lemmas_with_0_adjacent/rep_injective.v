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

Lemma rep_injective A B U : A <<= U -> B <<= U -> rep A U = rep B U -> A === B.
Proof.
intros D E F.
transitivity (rep A U).
-
symmetry.
apply rep_equi, D.
-
rewrite F.
apply rep_equi, E.
