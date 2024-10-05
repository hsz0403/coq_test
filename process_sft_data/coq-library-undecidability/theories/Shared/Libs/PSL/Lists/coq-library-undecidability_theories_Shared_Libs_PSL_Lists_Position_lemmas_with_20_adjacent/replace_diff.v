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
Admitted.

Lemma pos_elAt s A i : pos s A = Some i -> A .[i] = Some s.
Proof.
revert i s.
induction A; intros i s.
-
destruct i; inversion 1.
-
simpl.
decide (s = a).
+
inversion 1; subst; reflexivity.
+
Admitted.

Lemma elAt_app (A : list X) i B s : A .[i] = Some s -> (A ++ B).[i] = Some s.
Proof.
revert s B i.
Admitted.

Lemma elAt_el A (s : X) m : A .[ m ] = Some s -> s el A.
Proof.
revert A.
Admitted.

Lemma el_elAt (s : X) A : s el A -> exists m, A .[ m ] = Some s.
Proof.
Admitted.

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
Admitted.

Lemma nth_error_none A n l : nth_error l n = @None A -> length l <= n.
Proof.
revert n; induction l; intros n.
-
simpl; lia.
-
simpl.
intros.
destruct n.
inv H.
inv H.
assert (| l | <= n).
eauto.
Admitted.

Lemma pos_None (x : X) l l' : pos x l = None-> pos x l' = None -> pos x (l ++ l') = None.
Proof.
revert x l'; induction l; simpl; intros; eauto.
have (x = a).
destruct (pos x l) eqn:E; try congruence.
Admitted.

Lemma pos_first_S (x : X) l l' i : pos x l = Some i -> pos x (l ++ l') = Some i.
Proof.
revert x i; induction l; intros; simpl in *.
-
inv H.
-
decide (x = a); eauto.
destruct (pos x l) eqn:E.
+
eapply IHl in E.
now rewrite E.
+
Admitted.

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
Admitted.

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
Admitted.

Lemma replace_same xs x : replace xs x x = xs.
Proof.
Admitted.

Lemma replace_pos xs x y y' : x <> y -> x <> y' -> pos x xs = pos x (replace xs y y').
Proof.
induction xs; intros; simpl.
-
reflexivity.
-
repeat destruct Dec; try congruence; try lia; subst.
+
rewrite IHxs; eauto.
+
Admitted.

Lemma replace_diff xs x y : x <> y -> ~ x el replace xs x y.
Proof.
revert x y; induction xs; intros; simpl; try destruct _; firstorder.
