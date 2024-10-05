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

Lemma Union_wmon: wmonotonic TX TY (Union H).
Proof.
unfold Union; split.
intros R S HRS x y K; destruct K as [ i ]; exists i; apply (wmon_m (HH i) HRS); auto.
intros R HR x x' y Hxx' xRy; destruct xRy as [ i xRy ]; destruct (wmon_t (HH i) HR _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto; exists i; auto.
intros R S HR HS HRS HRS' a x x' y Hxx' xRy; destruct xRy as [ i xRy ]; destruct (wmon_a (HH i) HR HS HRS HRS' _ _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto; exists i; auto.
