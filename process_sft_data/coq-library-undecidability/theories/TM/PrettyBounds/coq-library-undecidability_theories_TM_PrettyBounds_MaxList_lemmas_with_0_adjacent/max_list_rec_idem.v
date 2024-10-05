From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Corollary max_list_rec_idem s xs : max_list_rec (max_list_rec s xs) xs = max_list_rec s xs.
Proof.
apply Nat.le_antisymm.
-
apply max_list_rec_lower_bound; eauto.
intros.
now apply max_list_rec_ge_el.
-
apply max_list_rec_lower_bound; eauto.
+
now rewrite <- !max_list_rec_ge.
+
intros.
rewrite <- max_list_rec_ge.
now apply max_list_rec_ge_el.
