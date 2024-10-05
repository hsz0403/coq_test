Require Import List.

Lemma in_rev : forall (A : Set) (a : A) (l : list A), In a l -> In a (rev l).
intros A a l H'.
apply rev_in with (A := A); auto.
rewrite (rev_involutive l); auto.
