Require Import List.

Lemma map_rev : forall (A B : Set) (f : A -> B) (l : list A), map f (rev l) = rev (map f l).
intros A B f l; elim l; simpl in |- *; auto.
intros a l0 H'; rewrite <- H'; simpl in |- *; auto.
apply trans_equal with (y := map f (rev l0) ++ map f (a :: nil)); auto.
apply map_app; auto.
