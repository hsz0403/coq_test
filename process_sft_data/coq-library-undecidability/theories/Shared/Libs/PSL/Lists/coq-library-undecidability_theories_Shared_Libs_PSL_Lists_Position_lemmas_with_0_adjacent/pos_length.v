From Undecidability.Shared.Libs.PSL Require Export BaseLists Dupfree.
Definition elAt := nth_error.
Notation "A '.[' i ']'" := (elAt A i) (no associativity, at level 50).
Section Fix_X.
Variable X : eqType.
Fixpoint pos (s : X) (A : list X) := match A with | nil => None | a :: A => if Dec (s = a) then Some 0 else match pos s A with None => None | Some n => Some (S n) end end.
Fixpoint replace (xs : list X) (y y' : X) := match xs with | nil => nil | x :: xs' => (if Dec (x = y) then y' else x) :: replace xs' y y' end.
End Fix_X.
Arguments replace {_} _ _ _.

Lemma pos_length (e : X) n E : pos e E = Some n -> n < |E|.
Proof.
revert e n; induction E; simpl; intros.
-
inv H.
-
decide (e = a).
+
inv H.
simpl.
lia.
+
destruct (pos e E) eqn:EE.
*
inv H.
assert (n1 < |E|) by eauto.
lia.
*
inv H.
