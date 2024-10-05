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

Lemma Comp_mon: monotonic TX TY (Comp G F).
Proof.
unfold Comp; split.
intros R S HRS; apply (mon_m HG (mon_m HF HRS)).
intros R S H H'; apply (mon_t HG (mon_t HF H H') (mon_m HF H')).
intros R S H H'; apply (mon_a HG).
intro l; destruct l.
apply (mon_t HF (H _) H').
apply (mon_a HF H H').
apply (mon_m HF H').
