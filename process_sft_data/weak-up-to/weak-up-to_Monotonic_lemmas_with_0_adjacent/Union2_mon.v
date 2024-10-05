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

Lemma Union2_mon: monotonic TX TY (Union2 F G).
Proof.
unfold Union2; split.
intros R S HRS x y H; destruct H; [ left; apply (mon_m HF HRS) | right; apply (mon_m HG HRS) ]; auto.
intros R S H H' x x' y Hxx' xRy; celim xRy; intro xRy; [ destruct (mon_t HF H H' _ _ _ Hxx' xRy) as [ y' ] | destruct (mon_t HG H H' _ _ _ Hxx' xRy) as [ y' ] ]; exists y'; auto; [ left | right ]; auto.
intros R S H H' a x x' y Hxx' xRy; celim xRy; intro xRy; [ destruct (mon_a HF H H' _ _ _ _ Hxx' xRy) as [ y' ] | destruct (mon_a HG H H' _ _ _ _ Hxx' xRy) as [ y' ] ]; exists y'; auto; [ left | right ]; auto.
