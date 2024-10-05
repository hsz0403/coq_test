From Undecidability.Shared.Libs.PSL Require Export BaseLists Dupfree.
Definition elAt := nth_error.
Notation "A '.[' i ']'" := (elAt A i) (no associativity, at level 50).
Section Fix_X.
Variable X : eqType.
Fixpoint pos (s : X) (A : list X) := match A with | nil => None | a :: A => if Dec (s = a) then Some 0 else match pos s A with None => None | Some n => Some (S n) end end.
Fixpoint replace (xs : list X) (y y' : X) := match xs with | nil => nil | x :: xs' => (if Dec (x = y) then y' else x) :: replace xs' y y' end.
End Fix_X.
Arguments replace {_} _ _ _.

Lemma pos_second_S x l l' i : pos x l = None -> pos x l' = Some i -> pos x (l ++ l') = Some ( i + |l| ).
Proof.
revert i l'; induction l; simpl; intros.
-
rewrite plus_comm.
eauto.
-
destruct _; subst; try congruence.
destruct (pos x l) eqn:EE.
congruence.
erewrite IHl; eauto.
