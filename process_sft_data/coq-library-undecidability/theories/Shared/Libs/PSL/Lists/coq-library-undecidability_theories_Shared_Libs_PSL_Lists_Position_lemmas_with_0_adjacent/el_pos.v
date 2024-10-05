From Undecidability.Shared.Libs.PSL Require Export BaseLists Dupfree.
Definition elAt := nth_error.
Notation "A '.[' i ']'" := (elAt A i) (no associativity, at level 50).
Section Fix_X.
Variable X : eqType.
Fixpoint pos (s : X) (A : list X) := match A with | nil => None | a :: A => if Dec (s = a) then Some 0 else match pos s A with None => None | Some n => Some (S n) end end.
Fixpoint replace (xs : list X) (y y' : X) := match xs with | nil => nil | x :: xs' => (if Dec (x = y) then y' else x) :: replace xs' y y' end.
End Fix_X.
Arguments replace {_} _ _ _.

Lemma el_pos s A : s el A -> exists m, pos s A = Some m.
Proof.
revert s; induction A; simpl; intros s H.
-
contradiction.
-
decide (s = a) as [D | D]; eauto; destruct H; try congruence.
destruct (IHA s H) as [n Hn]; eexists; now rewrite Hn.
