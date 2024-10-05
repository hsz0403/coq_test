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

Theorem add_frequency_list_not_in : forall m a b n, a <> b -> In (a, n) m -> In (a, n) (add_frequency_list b m).
Proof using.
intros m; elim m; clear m; simpl in |- *; auto.
intros (a1, l1) l H a0 b n H0 [H1| H1]; case (eqA_dec b a1); simpl in |- *; auto.
intros H2; case H0; injection H1; auto.
intros; apply trans_equal with (2 := sym_equal H2); auto.
