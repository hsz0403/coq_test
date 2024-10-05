Require Import List.

Lemma map_app : forall (A B : Set) (f : A -> B) (l1 l2 : list A), map f (l1 ++ l2) = map f l1 ++ map f l2.
intros A B f l1; elim l1; simpl in |- *; auto with datatypes.
intros a l H' l2; rewrite H'; auto.
