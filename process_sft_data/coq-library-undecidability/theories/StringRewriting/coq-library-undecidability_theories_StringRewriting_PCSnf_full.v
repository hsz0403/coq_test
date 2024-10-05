Require Import List.
Require Import Undecidability.PCP.PCP.
Definition string X := list X.
Notation "x / y" := (x, y).
Definition SRS X := list (string X * string X).
Inductive der {X : Type} (R : SRS X) : string X -> string X -> Prop := derB x u v : In (u / v) R -> der R (u ++ x) (x ++ v).
Inductive derv {X : Type} (R : SRS X) : string X -> string X -> Prop := derR z : derv R z z | derS x y z : der R x y -> derv R y z -> derv R x z.
Definition PCSnf : SRS nat * string nat * string nat -> Prop := fun '(R, x, y) => derv R x y.