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

Lemma power_extensional A B U : dupfree U -> A el power U -> B el power U -> A === B -> A = B.
Proof.
intros D E F G.
rewrite <- (rep_dupfree D E).
rewrite <- (rep_dupfree D F).
apply rep_eq, G.
