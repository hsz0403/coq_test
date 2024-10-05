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

Lemma UIter_wmon: wmonotonic TX TY (UIter F).
Proof.
unfold UIter.
change (fun R => union (UExp F R)) with (Union (fun n => (fun R => UExp F R n))).
apply Union_wmon; intro i; apply UExp_wmon.
