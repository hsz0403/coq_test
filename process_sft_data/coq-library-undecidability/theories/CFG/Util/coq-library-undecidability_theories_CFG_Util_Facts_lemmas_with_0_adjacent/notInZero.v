Require Import List Undecidability.Shared.ListAutomation Lia.
Import ListNotations ListAutomationNotations.
Fixpoint count (l : list nat) (n : nat) := match l with | [] => 0 | m :: l => if Nat.eqb n m then S (count l n) else count l n end.
Section fix_X.
Variable X:Type.
Implicit Types (A B: list X) (a b c: X).
End fix_X.

Lemma notInZero (x: nat) A : not (x el A) <-> count A x = 0.
Proof.
split; induction A.
-
reflexivity.
-
intros H.
cbn in *.
destruct (PeanoNat.Nat.eqb_spec x a).
+
exfalso.
apply H.
left.
congruence.
+
apply IHA.
intros F.
apply H.
now right.
-
tauto.
-
cbn.
destruct (PeanoNat.Nat.eqb_spec x a).
+
subst a.
lia.
+
intros H [E | E].
*
now symmetry in E.
*
tauto.
