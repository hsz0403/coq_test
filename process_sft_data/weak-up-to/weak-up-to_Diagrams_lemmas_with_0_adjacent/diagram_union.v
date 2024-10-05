Require Export Relations.
Set Implicit Arguments.
Section Def1.
Variables X X' Y Y': Type.
Variable RX: relation2 X X'.
Variable R: relation2 X Y.
Variable RY: relation2 Y Y'.
Variable R': relation2 X' Y'.
Definition diagram := forall x x' y, RX x x' -> R x y -> exists2 y', RY y y' & R' x' y'.
End Def1.
Section Def2.
Variable X: Type.
Variables R S: relation X.
Definition strong_commute := diagram R S R S.
Definition local_commute := diagram R S (star R) (star S).
Definition semi_commute := diagram R S (star R) S.
Definition commute := diagram (star R) (star S) (star R) (star S).
Definition confluent := diagram (star R) (star R) (star R) (star R).
End Def2.
Section Incl.
Variables X X' Y Y': Type.
Variable RX: relation2 X X'.
Variable R R': relation2 X Y.
Variable RY: relation2 Y Y'.
Variables S S': relation2 X' Y'.
Hypothesis H: diagram RX R RY S.
Hypothesis HR: forall x y, R' x y -> R x y.
Hypothesis HS: forall x y, S x y -> S' x y.
End Incl.
Section Reverse.
Variables X X' Y Y': Type.
Variable RX: relation2 X X'.
Variable R: relation2 X Y.
Variable RY: relation2 Y Y'.
Variable R': relation2 X' Y'.
Hypothesis H: diagram RX R RY R'.
End Reverse.
Section Compose.
Variables X Y Z X' Y' Z': Type.
Variable RY: relation2 Y Y'.
Variable RX: relation2 X X'.
Variable R1: relation2 X Y.
Variable R2: relation2 Y Z.
Variable RZ: relation2 Z Z'.
Variable S1: relation2 X' Y'.
Variable S2: relation2 Y' Z'.
Hypothesis H1: diagram RX R1 RY S1.
Hypothesis H2: diagram RY R2 RZ S2.
End Compose.
Section Union.
Variables X Y X' Y' I: Type.
Variable RX: relation2 X X'.
Variables R: I -> relation2 X Y.
Variable RY: relation2 Y Y'.
Variable S: relation2 X' Y'.
Hypothesis H: forall i, diagram RX (R i) RY S.
End Union.
Section Star.
Variables X X': Type.
Variable RX: relation2 X X'.
Variable R: relation X.
Variable S: relation X'.
Hypothesis H: diagram RX R RX (star S).
End Star.
Section Plus.
Variables X X': Type.
Variable RX: relation2 X X'.
Variable R: relation X.
Variable S: relation X'.
Hypothesis HR: diagram RX R RX (plus S).
End Plus.
Section PlusWf.
Variable X: Set.
Variable S: relation X.
Variable TX: relation X.
Hypothesis HS: diagram TX S (star TX) (plus S).
Hypothesis Hwf: well_founded (trans S).
Let Hpwf: well_founded (trans (plus S)) := plus_wf Hwf.
Variable TX': relation X.
Hypothesis HS': diagram TX' S (comp (star TX) TX') (plus S).
Variable Y: Type.
Variables R R': relation2 X Y.
Variable TY TY': relation Y.
Hypothesis HR: diagram TX R (star TY) (comp (star S) R).
Hypothesis HR': diagram TX' R (comp (star TY) TY') (comp (star S) R').
End PlusWf.
Section StarWf.
Variable X: Set.
Variable S: relation X.
Variable TX: relation X.
Hypothesis HS: local_commute TX S.
Hypothesis Hwf: well_founded (trans (comp (plus S) (plus TX))).
Section Gen.
Variable Y: Type.
Variable R: relation2 X Y.
Variable TY: relation Y.
Let SR := comp (star S) R.
Hypothesis HR: diagram TX R (star TY) SR.
Variables X' Y': Type.
Variable TaX: relation2 X X'.
Variable TaY: relation2 Y Y'.
Variable S' : relation2 X' X'.
Variable R' : relation2 X' Y'.
Let SR' := comp (star S') R'.
Let TAX := comp (star TX) TaX.
Let TAY := comp (star TY) TaY.
Hypothesis HT: diagram TaX S TAX (star S').
Hypothesis HRT: diagram TaX R TAY SR'.
End Gen.
End StarWf.

Theorem diagram_union: diagram RX (union R) RY S.
Proof.
intros x x' z Hxx' xRy; destruct xRy as [ i xRy ].
elim (H Hxx' xRy); intros y' Hyy' x'Sy'.
exists y'; assumption.
