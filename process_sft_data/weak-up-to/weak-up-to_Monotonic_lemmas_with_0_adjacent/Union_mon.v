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

Lemma Union_mon: monotonic TX TY (Union H).
Proof.
unfold Union; split.
intros R S HRS x y K; destruct K as [ i ]; exists i; apply (mon_m (HH i) HRS); auto.
intros R S HR HR' x x' y Hxx' xRy; destruct xRy as [ i xRy ]; destruct (mon_t (HH i) HR HR' _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto; exists i; auto.
intros R S HR HR' a x x' y Hxx' xRy; destruct xRy as [ i xRy ]; destruct (mon_a (HH i) HR HR' _ _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto; exists i; auto.
