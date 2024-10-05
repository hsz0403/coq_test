Require Import List Undecidability.Shared.ListAutomation Lia.
Import ListNotations ListAutomationNotations.
Fixpoint count (l : list nat) (n : nat) := match l with | [] => 0 | m :: l => if Nat.eqb n m then S (count l n) else count l n end.
Section fix_X.
Variable X:Type.
Implicit Types (A B: list X) (a b c: X).
End fix_X.

Lemma countSplit (A B: list nat) (x: nat) : count A x + count B x = count (A ++ B) x.
Proof.
induction A.
-
reflexivity.
-
cbn.
destruct (Nat.eqb x a).
+
cbn.
f_equal; exact IHA.
+
exact IHA.
