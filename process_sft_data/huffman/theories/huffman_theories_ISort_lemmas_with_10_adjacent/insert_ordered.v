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
Admitted.

Theorem isort_ordered : forall l : list A, ordered order (isort l).
Proof using order_fun_false order_fun_true.
Admitted.

Theorem isort_permutation : forall l : list A, permutation l (isort l).
Proof using.
intros l; elim l; clear l; simpl in |- *; auto.
intros a l H'.
Admitted.

Theorem insert_ordered : forall l : list A, ordered order l -> forall a : A, ordered order (insert a l).
Proof using order_fun_false order_fun_true.
intros l H'; elim H'; clear H' l; auto.
simpl in |- *; auto.
intros a b; simpl in |- *.
generalize (refl_equal (order_fun b a)); pattern (order_fun b a) at -1 in |- *; case (order_fun b a); intros Eq0; auto.
intros a b l H'0 H'1 H'2 a0.
simpl in |- *.
generalize (refl_equal (order_fun a0 a)); pattern (order_fun a0 a) at -1 in |- *; case (order_fun a0 a); intros Eq0; auto.
generalize (H'2 a0); simpl in |- *.
generalize (refl_equal (order_fun a0 b)); pattern (order_fun a0 b) at -1 in |- *; case (order_fun a0 b); intros Eq1; auto.
