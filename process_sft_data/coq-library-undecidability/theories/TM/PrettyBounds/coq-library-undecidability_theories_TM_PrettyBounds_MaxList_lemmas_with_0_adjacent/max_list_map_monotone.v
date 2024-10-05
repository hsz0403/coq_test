From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_map_monotone (X : Type) (f1 f2 : X -> nat) (xs : list X) : (forall (x : X), In x xs -> f1 x <= f2 x) -> max_list_map f1 xs <= max_list_map f2 xs.
Proof.
intros.
unfold max_list_map.
apply max_list_lower_bound.
intros ? (x&<-&?) % in_map_iff.
rewrite H.
apply max_list_ge.
apply in_map_iff.
eauto.
auto.
