From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_rec_monotone (xs : list nat) (s0 s1 : nat) : s0 <= s1 -> max_list_rec s0 xs <= max_list_rec s1 xs.
Proof.
revert s0 s1.
induction xs as [ | x' xs' IH]; intros; cbn in *.
-
assumption.
-
rewrite IH; eauto.
nia.
