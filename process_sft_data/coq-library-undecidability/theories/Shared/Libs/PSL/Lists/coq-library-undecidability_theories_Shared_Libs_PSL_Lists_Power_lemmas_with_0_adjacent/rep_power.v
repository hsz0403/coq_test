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

Lemma rep_power A U : rep A U el power U.
Proof.
revert A; induction U as [|x U]; intros A.
-
cbn; auto.
-
decide (x el A) as [H|H].
+
rewrite (rep_cons _ H).
cbn.
auto using in_map.
+
rewrite (rep_cons' _ H).
cbn.
auto.
