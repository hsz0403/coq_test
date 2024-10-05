From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_to_list_map (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) : map f (vector_to_list v) = vector_to_list (Vector.map f v).
Proof.
induction v.
-
cbn.
auto.
-
cbn.
f_equal.
auto.
