From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_rec_lower_bound (xs : list nat) (s : nat) (z : nat) : s <= z -> (forall x, In x xs -> x <= z) -> max_list_rec s xs <= z.
Proof.
revert s z.
induction xs as [ | x xs IH]; intros s z Hz Hxs; cbn in *.
-
assumption.
-
pose proof (Hxs x ltac:(eauto)) as Hxs'.
rewrite max_list_rec_max.
rewrite !IH by eauto.
nia.
