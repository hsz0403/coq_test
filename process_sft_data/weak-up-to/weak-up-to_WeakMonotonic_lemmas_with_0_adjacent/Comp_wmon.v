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

Lemma Comp_wmon: wmonotonic TX TY (Comp G F).
Proof.
unfold Comp; split.
intros R S HRS; apply (wmon_m HG); apply (wmon_m HF); exact HRS.
intros R HR; exact (wmon_t HG (wmon_t HF HR)).
intros R S HR HS HRS HRS'; apply (wmon_a HG).
apply (wmon_t HF HR).
apply (wmon_t HF HS).
exact (wmon_a HF HR HS HRS HRS').
apply (wmon_m HF HRS').
