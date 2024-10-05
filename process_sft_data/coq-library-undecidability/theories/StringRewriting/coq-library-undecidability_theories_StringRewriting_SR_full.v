Require Import List.
Require Import Undecidability.PCP.PCP.
Definition string X := list X.
Module RuleNotation.
Notation "x / y" := (x, y).
End RuleNotation.
Import RuleNotation.
Definition SRS X := list (string X * string X).
Inductive rew {X : Type} (R : SRS X) : string X -> string X -> Prop := rewB x y u v : In (u / v) R -> rew R (x ++ u ++ y) (x ++ v ++ y).
Inductive rewt {X : Type} (R : SRS X) : string X -> string X -> Prop := rewR z : rewt R z z | rewS x y z : rew R x y -> rewt R y z -> rewt R x z.
Definition SR : SRS nat * string nat * string nat -> Prop := fun '(R, x, y) => rewt R x y.
Definition SRH : SRS nat * string nat * nat -> Prop := fun '(R, x, a) => exists y, rewt R x y /\ In a y.
Definition swap {X Y} : X * Y -> Y * X := fun '(x,y) => (y,x).
Definition TSR : SRS nat * string nat * string nat -> Prop := fun '(R, x, y) => rewt (R ++ map swap R) x y.
Definition TSRH : SRS nat * string nat * nat -> Prop := fun '(R, x, a) => exists y, rewt (R ++ map swap R) x y /\ In a y.