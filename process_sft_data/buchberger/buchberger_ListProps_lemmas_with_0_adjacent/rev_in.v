Require Import List.

Lemma rev_in : forall (A : Set) (a : A) (l : list A), In a (rev l) -> In a l.
intros A a l; elim l; simpl in |- *; auto.
intros a0 l0 H' H'0.
case (in_app_or _ _ _ H'0); simpl in |- *; intros H'1; auto.
elim H'1; auto.
intros H'2; elim H'2.
