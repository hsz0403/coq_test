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

Theorem add_frequency_list_unique_key : forall (a : A) l, unique_key l -> unique_key (add_frequency_list a l).
Proof using.
intros a l; elim l; simpl in |- *; auto.
intros (a1, n1) l1 Rec H; case (eqA_dec a a1).
intros e; apply unique_key_perm with (l1 := (a, S n1) :: l1); auto.
apply unique_key_cons; auto.
intros b; red in |- *; intros H0; case (unique_key_in _ _ _ _ b _ H); auto.
rewrite <- e; auto.
apply unique_key_inv with (1 := H); auto.
intros n; apply unique_key_cons; auto.
intros b; red in |- *; intros H0; case add_frequency_list_in_inv with (1 := H0); auto.
intros H2; case (unique_key_in _ _ _ _ b _ H); auto.
apply Rec; apply unique_key_inv with (1 := H); auto.
