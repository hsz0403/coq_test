Require Import List.
Import ListNotations.
Definition poly : Set := list nat.
Inductive polyc : Set := | polyc_one : nat -> polyc | polyc_sum : nat -> nat -> nat -> polyc | polyc_prod : nat -> nat -> polyc.
Definition poly_eq (p q: poly) : Prop := forall i, nth i p 0 = nth i q 0.
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).
Fixpoint poly_add (p q: poly) : poly := match p, q with | [], q => q | p, [] => p | (c :: p), (d :: q) => (c + d) :: poly_add p q end.
Fixpoint poly_mult (p q: poly) : poly := match p with | [] => [] | (c :: p) => poly_add (map (fun a => c * a) q) (0 :: (poly_mult p q)) end.
Definition polyc_sem (φ: nat -> poly) (c: polyc) := match c with | polyc_one x => φ x ≃ [1] | polyc_sum x y z => φ x ≃ poly_add (φ y) (φ z) | polyc_prod x y => φ x ≃ poly_mult [0; 1] (φ y) end.
Definition LPolyNC_SAT (l : list polyc) := exists φ, forall c, In c l -> polyc_sem φ c.