From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Corollary max_list_rec_max' (xs : list nat) (s1 s2 : nat) : max_list_rec (Init.Nat.max s1 s2) xs = Init.Nat.max s1 (max_list_rec s2 xs).
Proof.
apply Nat.le_antisymm.
-
apply max_list_rec_lower_bound; eauto.
+
apply Nat.max_le_compat_l.
apply max_list_rec_ge.
+
intros x Hx.
rewrite <- Max.le_max_r.
now apply max_list_rec_ge_el.
-
rewrite max_list_rec_max.
apply Nat.max_le_compat; auto.
apply max_list_rec_ge.
