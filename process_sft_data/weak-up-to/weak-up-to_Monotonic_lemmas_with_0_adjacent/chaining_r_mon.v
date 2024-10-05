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

Lemma chaining_r_mon: simulation TY TY T -> monotonic TX TY (chaining_r T).
Proof.
intro H; apply mkmon; unfold chaining_r; intros U V HUV.
intros x y L; destruct L as [ w ]; exists w; auto.
intros HUV' x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ]; destruct (HUV _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ]; destruct (weak_strong H _ _ _ _ Hww' wRy) as [ y' Hyy' w'Ry' ].
exists y'; auto; exists w'; auto.
intros HUV' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ]; destruct (HUV _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ]; destruct (weak_strong H _ _ _ _ Hww' wRy) as [ y' Hyy' w'Ry' ].
exists y'; auto; exists w'; auto.
