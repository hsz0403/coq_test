From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma max_list_rec_el_or_eq xs s : max_list_rec s xs el xs \/ max_list_rec s xs = s /\ (forall x : nat, x el xs -> x <= s).
Proof.
revert s.
induction xs as [ | x xs IH]; intros; cbn in *; eauto.
rewrite !max_list_rec_max.
assert (max_list_rec s xs <= max_list_rec x xs \/ max_list_rec x xs <= max_list_rec s xs) as [H|H] by lia.
-
rewrite !max_l by assumption.
specialize (IH x) as [IH|[<- IH]].
+
left.
eauto.
+
rewrite !max_list_rec_idem.
auto.
-
rewrite !max_r by assumption.
specialize (IH s) as [IH|[<- IH]].
+
left.
eauto.
+
right.
split.
*
apply max_list_rec_idem.
*
intros y [<-|Hy].
--
rewrite <- H.
apply max_list_rec_ge.
--
now apply IH.
