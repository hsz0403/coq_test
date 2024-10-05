From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_rec_irrelevant (xs : list nat) (s1 s2 : nat) : xs <> nil -> (forall x, In x xs -> s1 <= x /\ s2 <= x) -> max_list_rec s1 xs = max_list_rec s2 xs.
Proof.
induction xs as [ | x xs IH]; intros Hneq Hxs; cbn in *.
-
congruence.
-
pose proof (Hxs x ltac:(auto)) as [Hxs1 Hxs2].
destruct xs as [ | x' xs].
+
cbn.
nia.
+
rewrite !max_list_rec_max.
rewrite IH; eauto.
congruence.
