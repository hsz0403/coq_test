Require Import List.
Import ListNotations.
Definition stack (X : Type) := list (list X * list X).
Fixpoint sigma {X: Type} (a : X) (A : stack X) := match A with nil => [a] | (x, y) :: A => x ++ (sigma a A) ++ y end.
Definition CFPP : stack nat * nat -> Prop := fun '(R, a) => exists (A : stack nat), incl A R /\ A <> [] /\ sigma a A = rev (sigma a A).
Definition CFPI : stack nat * stack nat * nat -> Prop := fun '(R1, R2, a) => exists (A1 A2 : stack nat), incl A1 R1 /\ incl A2 R2 /\ A1 <> [] /\ A2 <> [] /\ sigma a A1 = sigma a A2.