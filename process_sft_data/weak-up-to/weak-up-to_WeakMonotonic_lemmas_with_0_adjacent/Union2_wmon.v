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

Lemma Union2_wmon: wmonotonic TX TY (Union2 F G).
Proof.
unfold Union2; split.
intros R S HRS x y H; destruct H; [ left; apply (wmon_m HF HRS) | right; apply (wmon_m HG HRS) ]; auto.
intros R HR x x' y Hxx' xRy; celim xRy; intro xRy; [ destruct (wmon_t HF HR _ _ _ Hxx' xRy) as [ y' ] | destruct (wmon_t HG HR _ _ _ Hxx' xRy) as [ y' ] ]; exists y'; auto; [ left | right ]; auto.
intros R S HR HS HRS HRS' a x x' y Hxx' xRy; celim xRy; intro xRy; [ destruct (wmon_a HF HR HS HRS HRS' _ _ _ _ Hxx' xRy) as [ y' ] | destruct (wmon_a HG HR HS HRS HRS' _ _ _ _ Hxx' xRy) as [ y' ] ]; exists y'; auto; [ left | right ]; auto.
