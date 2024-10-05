Require Import Arith.
Fixpoint naryFunc (n : nat) : Set := match n with | O => nat | S n => nat -> naryFunc n end.
Fixpoint naryRel (n : nat) : Set := match n with | O => bool | S n => nat -> naryRel n end.
Definition extEqual (n : nat) (a b : naryFunc n) : Prop.
intros.
induction n as [| n Hrecn].
exact (a = b).
exact (forall c : nat, Hrecn (a c) (b c)).
Defined.
Fixpoint charFunction (n : nat) : naryRel n -> naryFunc n := match n return (naryRel n -> naryFunc n) with | O => fun R : bool => match R with | true => 1 | false => 0 end | S m => fun (R : naryRel (S m)) (a : nat) => charFunction m (R a) end.

Definition extEqual (n : nat) (a b : naryFunc n) : Prop.
intros.
induction n as [| n Hrecn].
exact (a = b).
exact (forall c : nat, Hrecn (a c) (b c)).
