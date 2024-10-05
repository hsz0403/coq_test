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

Theorem number_of_occurrences_permutation : forall l1 l2 a, permutation l1 l2 -> number_of_occurrences a l1 = number_of_occurrences a l2.
Proof using.
intros l1 l2 a H; generalize a; elim H; clear H a l1 l2; simpl in |- *; auto.
intros a L1 L2 H H0 a0; case (eqA_dec a a0); simpl in |- *; auto; case (eqA_dec a0 a); simpl in |- *; auto.
intros a b L a0; case (eqA_dec a0 a); simpl in |- *; auto; case (eqA_dec a0 b); simpl in |- *; auto.
intros L1 L2 L3 H H0 H1 H2 a; apply trans_equal with (1 := H0 a); auto.
