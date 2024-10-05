Require Import List Undecidability.Shared.ListAutomation Lia.
Import ListNotations ListAutomationNotations.
Fixpoint count (l : list nat) (n : nat) := match l with | [] => 0 | m :: l => if Nat.eqb n m then S (count l n) else count l n end.
Section fix_X.
Variable X:Type.
Implicit Types (A B: list X) (a b c: X).
End fix_X.

Lemma rev_eq A B: List.rev A = List.rev B <-> A = B.
Proof.
split.
-
intros H%(f_equal (@rev X)).
now rewrite !rev_involutive in H.
-
now intros <-.
