From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_rec_ge_el (xs : list nat) (s : nat) (x : nat) : In x xs -> x <= max_list_rec s xs.
Proof.
induction xs as [ | x' xs IH] in s,x|-*; intros Hel; cbn in *.
-
tauto.
-
destruct Hel as [ <- | Hel].
+
rewrite max_list_rec_max.
rewrite <- Nat.le_max_l.
apply max_list_rec_ge.
+
rewrite max_list_rec_max.
rewrite <- IH; eauto.
nia.
