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

Lemma extEqualTrans : forall (n : nat) (a b c : naryFunc n), extEqual n a b -> extEqual n b c -> extEqual n a c.
Proof.
intros.
induction n as [| n Hrecn].
simpl in |- *.
transitivity b; auto.
simpl in |- *.
intros.
eapply Hrecn.
simpl in H.
apply (H c0).
apply (H0 c0).
