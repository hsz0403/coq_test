From Undecidability.TM.Util Require Export Prelim ArithPrelim.
Fixpoint max_list_rec (s : nat) (xs : list nat) { struct xs } : nat := match xs with | nil => s | x :: xs' => max_list_rec (max x s) xs' end.
Definition max_list (xs : list nat) := max_list_rec 0 xs.
Section max_list_map.
Variable (X : Type) (f : X -> nat).
Definition max_list_map (xs : list X) := max_list (map f xs).
Definition max_list_map_rec (s : nat) (xs : list X) := max_list_rec s (map f xs).
End max_list_map.

Lemma upperBound_In (xs : list nat) (u : nat) : (forall x, In x xs -> x <= u) -> (In u xs) \/ (~ In u xs /\ forall x, In x xs -> x < u).
Proof.
intros HUb.
induction xs as [ | x xs IH]; intros; cbn in *.
-
right.
auto.
-
spec_assert IH as [IH | [IH1 IH2]] by auto.
+
auto.
+
decide (x = u) as [ <- | Hdec].
*
left.
auto.
*
right.
split.
--
intros [<- | H]; congruence.
--
intros y [-> | H].
++
specialize (HUb y ltac:(now left)).
lia.
++
specialize (IH2 y H).
lia.
