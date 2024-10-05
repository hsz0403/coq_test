Require Export Settings.
Set Implicit Arguments.
Section Global.
Variable A: Type.
Section A.
Variables X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Section A'.
Variable R: relation2 X Y.
Variable E: relation2 X X.
Variable T: relation2 Y Y.
End A'.
Variables F G: function X Y.
Hypothesis HF: monotonic TX TY F.
Hypothesis HG: monotonic TX TY G.
Section Union.
Variable I: Type.
Variable H: I -> function X Y.
Hypothesis HH: forall i, monotonic TX TY (H i).
End Union.
End A.
Section B.
Variables X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variables F G: function X Y.
Hypothesis HF: monotonic TX TY F.
Hypothesis HG: monotonic TX TY G.
End B.
End Global.

Lemma chaining_l_mon: expansion1 TX TX E -> monotonic TX TY (chaining_l E).
Proof.
clear R.
intro HS; split.
intros R S H x y XY; destruct XY as [ w XW WY ]; exists w; auto.
intros R S H H' x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
destruct (HS _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
celim Hww'; intro Hww'.
exists y; auto; exists w'; auto; destruct Hww'; apply H'; auto.
destruct (H _ _ _ Hww' wRy) as [ y' Hyy' w'Ry' ]; exists y'; auto; exists w'; auto.
intros R S H H' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
destruct (HS _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
destruct (H _ _ _ _ Hww' wRy) as [ y' Hyy' w'Ry' ]; exists y'; auto; exists w'; auto.
