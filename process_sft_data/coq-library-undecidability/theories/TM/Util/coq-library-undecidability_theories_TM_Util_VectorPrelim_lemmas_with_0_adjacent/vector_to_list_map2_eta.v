From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_to_list_map2_eta (X Y Z : Type) (n : nat) (f : X -> Y -> Z) (xs : Vector.t X (S n)) (ys : Vector.t Y (S n)) : f (Vector.hd xs) (Vector.hd ys) :: vector_to_list (Vector.map2 f (Vector.tl xs) (Vector.tl ys)) = vector_to_list (Vector.map2 f xs ys).
Proof.
now destruct_vector.
