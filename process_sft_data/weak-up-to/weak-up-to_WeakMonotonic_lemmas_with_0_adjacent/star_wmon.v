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

Lemma star_wmon: wmonotonic TX TX (star (X:=X)).
Proof.
split.
intros R S H x y XY; induction XY as [ x | w x y XW WY IH ]; auto; apply S_star with w; auto.
intros R HR; unfold simulation_t, evolve_t, evolve_1.
apply diagram_reverse; apply diagram_incl with (Weak TX (T _)) (Weak TX (T _)); auto; apply diagram_reverse.
apply diagram_star; apply diagram_incl with R R; auto; apply weak_strong_t; exact HR.
intros R S HR HS HRS HRS' a; unfold evolve_1.
apply diagram_reverse; apply diagram_incl with (Weak TX (L a)) (Weak TX (L a)); auto; apply diagram_reverse.
intros x x' y Hxx' xRy; cgen Hxx'; cgen x'; induction xRy as [ x | w x y xRw wRy IH ]; intros x' Hxx'.
exists x'; auto.
destruct Hxx' as [ x1 Hxx1 Hx1x' ]; destruct Hx1x' as [ x2 Hx1x2 Hx2x' ].
destruct (weak_strong_t HR _ Hxx1 xRw) as [ w1 Hww1 x1Rw1 ].
destruct (HRS _ _ _ _ Hx1x2 x1Rw1) as [ w2 Hw1w2 x2Rw2 ].
destruct (weak_strong_t HS _ Hx2x' x2Rw2) as [ w' Hw2w' x'Rw' ].
elim IH with w'.
intros y' Hyy' w'Ry'; exists y'; auto; apply S_star with w'; auto.
apply taus_weak with w1; auto; apply weak_taus with w2; auto.
