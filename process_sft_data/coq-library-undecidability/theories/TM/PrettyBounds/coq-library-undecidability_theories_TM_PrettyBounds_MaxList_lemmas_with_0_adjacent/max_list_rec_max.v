From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_rec_max (xs : list nat) (s1 s2 : nat) : max_list_rec (max s1 s2) xs = max (max_list_rec s1 xs) (max_list_rec s2 xs).
Proof.
induction xs as [ | x xs IH] in s1,s2|-*; cbn in *.
-
reflexivity.
-
rewrite Max.max_assoc.
rewrite !IH.
nia.
