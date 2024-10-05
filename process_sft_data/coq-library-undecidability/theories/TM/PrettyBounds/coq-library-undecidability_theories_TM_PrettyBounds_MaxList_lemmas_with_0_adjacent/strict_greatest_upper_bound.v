From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma strict_greatest_upper_bound : forall (xs : list nat) (M s : nat), (In M xs \/ (M = s /\ forall x, In x xs -> x <= s)) -> (s <= M) -> (forall x, In x xs -> x < M) -> (forall x, In x xs -> x < s).
Proof.
intros xs.
induction xs as [ | x xs IH]; intros M s HM1 Hs HM2 y Hy; cbn in *.
-
auto.
-
destruct Hy as [ <- | Hy].
+
destruct HM1 as [ [ <- | HM1] | (->&HM1)]; eauto.
*
exfalso.
specialize (HM2 x ltac:(eauto)).
nia.
*
rewrite HM2; eauto.
+
destruct HM1 as [ [ <- | HM1] | (->&HM1)]; eauto.
exfalso.
specialize (HM2 x ltac:(eauto)).
nia.
