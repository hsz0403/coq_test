Require Import List Undecidability.Shared.ListAutomation Lia.
Import ListNotations ListAutomationNotations.
Fixpoint count (l : list nat) (n : nat) := match l with | [] => 0 | m :: l => if Nat.eqb n m then S (count l n) else count l n end.
Section fix_X.
Variable X:Type.
Implicit Types (A B: list X) (a b c: X).
End fix_X.

Lemma last_app_eq A B a b : A++[a] = B++[b] -> A = B /\ a = b.
Proof.
intros H%(f_equal (@rev X)).
rewrite !rev_app_distr in H.
split.
-
inv H.
apply (f_equal (@rev X)) in H2.
now rewrite !rev_involutive in H2.
-
now inv H.
