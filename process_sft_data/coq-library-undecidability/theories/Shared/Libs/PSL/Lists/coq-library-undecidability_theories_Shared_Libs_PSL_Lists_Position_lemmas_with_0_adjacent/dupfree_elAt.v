From Undecidability.Shared.Libs.PSL Require Export BaseLists Dupfree.
Definition elAt := nth_error.
Notation "A '.[' i ']'" := (elAt A i) (no associativity, at level 50).
Section Fix_X.
Variable X : eqType.
Fixpoint pos (s : X) (A : list X) := match A with | nil => None | a :: A => if Dec (s = a) then Some 0 else match pos s A with None => None | Some n => Some (S n) end end.
Fixpoint replace (xs : list X) (y y' : X) := match xs with | nil => nil | x :: xs' => (if Dec (x = y) then y' else x) :: replace xs' y y' end.
End Fix_X.
Arguments replace {_} _ _ _.

Lemma dupfree_elAt (A : list X) n m s : dupfree A -> A.[n] = Some s -> A.[m] = Some s -> n = m.
Proof with try tauto.
intros H; revert n m; induction A; simpl; intros n m H1 H2.
-
destruct n; inv H1.
-
destruct n, m; inv H...
+
inv H1.
simpl in H2.
eapply elAt_el in H2...
+
inv H2.
simpl in H1.
eapply elAt_el in H1...
+
inv H1.
inv H2.
rewrite IHA with n m...
