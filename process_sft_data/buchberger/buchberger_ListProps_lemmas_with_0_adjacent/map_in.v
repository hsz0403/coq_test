Require Import List.

Lemma map_in : forall (A B : Set) (f : A -> B) (b : B) (xs : list A), In b (map f xs) -> ex (fun a : A => b = f a /\ In a xs).
intros A B f b xs; elim xs; simpl in |- *; auto.
intros H'; elim H'; auto.
intros a l H' H'0; elim H'0; [ intros H'1; clear H'0 | intros H'1; clear H'0 ]; auto.
exists a; split; auto.
elim H'; [ intros a0 E; elim E; intros H'2 H'3; clear E H' | clear H' ]; auto.
exists a0; split; auto.
