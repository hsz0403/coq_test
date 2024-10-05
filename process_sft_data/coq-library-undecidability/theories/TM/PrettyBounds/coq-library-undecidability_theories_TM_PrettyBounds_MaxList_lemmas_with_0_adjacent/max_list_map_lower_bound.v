From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_map_lower_bound (xs : list X) (z : nat) : (forall x, In x xs -> f x <= z) -> max_list_map xs <= z.
Proof.
intros.
unfold max_list_map.
apply max_list_lower_bound.
intros ? (?&<-&?) % in_map_iff.
auto.
