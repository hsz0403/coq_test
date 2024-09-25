Require Import Coq.Unicode.Utf8.
Require Import List.

Ltac reduce_eq := simpl; reflexivity.

Theorem my_first_proof : (forall A : Prop, A -> A).
Proof.
