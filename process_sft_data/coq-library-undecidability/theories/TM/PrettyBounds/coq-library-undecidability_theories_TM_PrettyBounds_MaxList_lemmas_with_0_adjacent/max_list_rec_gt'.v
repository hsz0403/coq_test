From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Corollary max_list_rec_gt' xs s : (forall x : nat, x el xs -> x < max_list_rec s xs) -> max_list_rec s xs = s /\ (forall x : nat, x el xs -> x < s).
Proof.
split.
-
revert H.
generalize (max_list_rec_ge xs s) as L1.
set (m := (max_list_rec s xs)).
intros.
enough (m <= s) by nia.
apply max_list_rec_lower_bound; auto.
intros x Hx.
apply Nat.lt_le_incl.
eapply max_list_rec_gt; eauto.
-
now apply max_list_rec_gt.
