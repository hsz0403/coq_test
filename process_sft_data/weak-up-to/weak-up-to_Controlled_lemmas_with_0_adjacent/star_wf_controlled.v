Require Export Theory.
Set Implicit Arguments.
Section RelaxedExpansion.
Variables A X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variable B: relation X.
Hypothesis HB: wexpansion1 TX TX B.
Let wexpansion1_ctrl_t: forall R, evolve_t TX TY R (comp (star B) R) -> simulation_t TX TY (comp (star B) R).
Proof.
intros R HR x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
cgen Hxx'; cgen x'; induction xRw as [ x | z x w xRz zRw IH ]; intros x' Hxx'.
apply (HR _ _ _ Hxx' wRy).
destruct (HB Hxx' xRz) as [ z' Hzz' x'Rz' ].
celim Hzz'; intro Hzz'.
destruct Hzz'; exists y; auto; exists w; auto; apply star_trans with z; auto.
destruct (IH wRy _ Hzz') as [ y' Hyy' z'Ry' ] ; destruct z'Ry' as [ w' ].
exists y'; auto; exists w'; auto; apply S_star with z'; auto.
End RelaxedExpansion.
Section PlusWf.
Variable A: Type.
Variable X: Set.
Variable Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variable B: relation X.
Hypothesis HB: evolve TX TX B (plus B).
Hypothesis HB': well_founded (trans B).
End PlusWf.
Section StarWf.
Variable A: Type.
Variable X: Set.
Variable Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variable B: relation X.
Hypothesis HB: evolve TX TX B (star B).
Hypothesis HB': well_founded (trans (comp (plus B) (plus (TX (T _))))).
End StarWf.

Theorem star_wf_controlled: controlled TX TY B.
Proof.
split.
intros R HR; unfold simulation_t, evolve_t, evolve_1, Weak.
apply diagram_reverse; apply diagram_incl with (star (TX (T _))) (star (TY (T _))); auto; apply diagram_reverse.
apply diagram_star_wf_1; auto; exact (HB (l:=T _)).
intros R S HR HS HRS HRS' a; unfold evolve_1.
apply diagram_reverse; apply diagram_incl with (Weak TX (L a)) (Weak TY (L a)); auto; apply diagram_reverse.
unfold Weak; apply diagram_star_wf_2; auto; try exact (HB (l:=T _)); intros x x' y Hxx' xRy; destruct Hxx' as [ x1 Hxx1 Hx1x' ].
destruct (HB Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
destruct (diagram_star_wf (HB (l:=T _)) HB' Hx1x' x1Ry1) as [ y' Hy1y' x'Ry' ].
exists y'; auto; fold (Weak TX (L a)); apply weak_taus with y1; auto.
destruct (HRS _ _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
destruct (weak_strong_t HS _ Hx1x' x1Ry1) as [ y' Hy1y' x'Ry' ]; exists y'.
fold (Weak TY (L a)); apply weak_taus with y1; auto.
exists x'; auto.
