Require Import List Undecidability.Shared.ListAutomation Lia.
Import ListNotations ListAutomationNotations.
Fixpoint count (l : list nat) (n : nat) := match l with | [] => 0 | m :: l => if Nat.eqb n m then S (count l n) else count l n end.
Section fix_X.
Variable X:Type.
Implicit Types (A B: list X) (a b c: X).
End fix_X.

Lemma rev_nil A: rev A = [] -> A = [].
Proof.
destruct A.
auto.
now intros H%eq_sym%app_cons_not_nil.
