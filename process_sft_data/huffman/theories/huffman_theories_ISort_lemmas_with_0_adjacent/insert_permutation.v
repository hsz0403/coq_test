Require Import List.
From Huffman Require Import Permutation.
From Huffman Require Import Ordered.
Section ISortExample.
Variable A : Type.
Variable order : A -> A -> Prop.
Variable order_fun : A -> A -> bool.
Hypothesis order_fun_true : forall a b : A, order_fun a b = true -> order a b.
Hypothesis order_fun_false : forall a b : A, order_fun a b = false -> order b a.
Fixpoint insert (a : A) (l : list A) {struct l} : list A := match l with | [] => a :: [] | b :: l1 => match order_fun a b with | true => a :: l | false => b :: insert a l1 end end.
Hint Resolve insert_ordered insert_permutation : core.
Fixpoint isort (l : list A) : list A := match l with | [] => [] | b :: l1 => insert b (isort l1) end.
Hint Resolve isort_ordered isort_permutation : core.
End ISortExample.
Arguments insert [A].
Arguments isort [A].

Theorem insert_permutation : forall (L : list A) (a : A), permutation (a :: L) (insert a L).
Proof using.
intros L; elim L; simpl in |- *; auto.
intros b l H' a.
case_eq (order_fun a b); intros H1; auto.
apply permutation_trans with (l2 := b :: a :: l); auto.
