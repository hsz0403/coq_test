From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Corollary max_list_rec_In (xs : list nat) (s : nat) : (max_list_rec s xs = s /\ forall x, In x xs -> x < s) \/ In (max_list_rec s xs) xs.
Proof.
pose proof @upperBound_In xs (max_list_rec s xs).
spec_assert H as [H | [H1 H2]].
-
intros.
now apply max_list_rec_ge_el.
-
now right.
-
left.
now apply max_list_rec_gt'.
