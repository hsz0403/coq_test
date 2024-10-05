Require Export Monotonic.
Set Implicit Arguments.
Section Global.
Variable A: Type.
Section A.
Variables X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variables F G: function X Y.
Hypothesis HF: wmonotonic TX TY F.
Hypothesis HG: wmonotonic TX TY G.
Section Union.
Variable I: Type.
Variable H: I -> function X Y.
Hypothesis HH: forall i, wmonotonic TX TY (H i).
End Union.
End A.
Section B.
Variables X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variables F G: function X Y.
Hypothesis HF: wmonotonic TX TY F.
Hypothesis HG: wmonotonic TX TY G.
End B.
Section C.
Variables X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variables F G: function X X.
Hypothesis HF: wmonotonic TX TX F.
Hypothesis HG: wmonotonic TX TX G.
Variable L: relation Y.
Hypothesis HL: simulation TY TY L.
End C.
End Global.

Lemma Chaining_wmon: wmonotonic TX TX (Chain F G).
Proof.
unfold Chain; split.
intros R S HRS x y H; destruct H as [ w H1 H2 ]; exists w; [ apply (wmon_m HF HRS) | apply (wmon_m HG HRS) ]; auto.
intros R HR x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
destruct (wmon_t HF HR _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
destruct (weak_strong_t (wmon_t HG HR) _ Hww' wRy) as [ y' Hyy' x'Ry' ].
exists y'; auto; exists w'; auto.
intros R S HR HS HRS HRS' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
destruct (wmon_a HF HR HS HRS HRS' _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
destruct Hww' as [ w1 Hww1 Hw1w' ]; destruct Hw1w' as [ w2 Hw1w2 Hw2w' ].
destruct (weak_strong_t (wmon_t HG HR) _ Hww1 wRy) as [ y1 Hyy1 w1Ry1 ].
destruct (wmon_a HG HR HS HRS HRS' _ _ _ _ Hw1w2 w1Ry1) as [ y2 Hy1y2 w2Ry2 ].
destruct (weak_strong_t (wmon_t HG HS) _ Hw2w' w2Ry2) as [ y' Hy2y' w'Ry' ].
exists y'.
apply taus_weak with y1; auto; apply weak_taus with y2; auto.
exists w'; auto.
