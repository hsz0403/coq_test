From Huffman Require Import AuxLib.
Require Import List.
From Huffman Require Import UniqueKey.
From Huffman Require Import Permutation.
Section Frequency.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Fixpoint id_list (a : A) (n : nat) {struct n} : list A := match n with | O => [] | S n1 => a :: id_list a n1 end.
Fixpoint add_frequency_list (a : A) (l : list (A * nat)) {struct l} : list (A * nat) := match l with | [] => (a, 1) :: [] | (b, n) :: l1 => match eqA_dec a b with | left _ => (a, S n) :: l1 | right _ => (b, n) :: add_frequency_list a l1 end end.
Fixpoint frequency_list (l : list A) : list (A * nat) := match l with | [] => [] | a :: l1 => add_frequency_list a (frequency_list l1) end.
Hint Resolve frequency_list_unique : core.
Hint Resolve in_frequency_map : core.
Fixpoint number_of_occurrences (a : A) (l : list A) {struct l} : nat := match l with | [] => 0 | b :: l1 => match eqA_dec a b with | left _ => S (number_of_occurrences a l1) | right _ => number_of_occurrences a l1 end end.
End Frequency.
Arguments id_list [A].
Arguments add_frequency_list [A].
Arguments frequency_list [A].
Arguments number_of_occurrences [A].
Hint Resolve in_frequency_map : core.
Hint Resolve frequency_list_unique : core.

Theorem number_of_occurrences_permutation_ex : forall (m : list A) (a : A), exists m1 : list A, permutation m (id_list a (number_of_occurrences a m) ++ m1) /\ ~ In a m1.
Proof using.
intros m; elim m; simpl in |- *; auto.
intros a; exists []; split; auto with datatypes.
intros a l H a0.
case (eqA_dec a0 a); simpl in |- *; intros H1.
case (H a0); intros m1 (H2, H3).
exists m1; split; auto.
pattern a0 at 1 in |- *; rewrite H1; auto.
case (H a0); intros m1 (H2, H3).
exists (a :: m1); split; auto.
apply permutation_trans with ((a :: m1) ++ id_list a0 (number_of_occurrences a0 l)); auto.
simpl in |- *; apply permutation_skip; auto.
apply permutation_trans with (1 := H2); auto.
simpl in |- *; contradict H3; case H3; intros H4; auto; case H1; auto.
