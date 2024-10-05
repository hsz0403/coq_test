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

Lemma UExp_mon: forall n, monotonic TX TY (fun R => UExp F R n).
Proof.
intro n; induction n as [ | n IH ].
apply (identity_mon TX TY).
simpl; fold (Union2 (fun R => UExp F R n) (fun R => F (UExp F R n))).
apply Union2_mon; auto.
fold (Comp F (fun R => UExp F R n)).
apply Comp_mon; auto.
