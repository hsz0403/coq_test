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

Theorem wexpansion1_ctrl: wexpansion1 TX TX B -> controlled TX TY B.
Proof.
split; auto.
intros R S HR HS HRS HRS' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
cgen Hxx'; cgen x'; induction xRw as [ x | z x w xRz zRw IH ]; intros x' Hxx'.
destruct (HRS _ _ _ _ Hxx' wRy) as [ y' Hyy' w'Ry' ]; exists y'; auto; exists x'; auto.
destruct (HB Hxx' xRz) as [ z' Hzz' x'Rz' ].
destruct Hzz' as [ z1 Hzz1 Hz1z' ].
destruct (IH wRy _ Hzz1) as [ y1 Hyy1 z1Ry1 ].
cut (simulation_t TX TY (comp (star B) S)).
intro HS'; destruct (weak_strong_t HS' _ Hz1z' z1Ry1) as [ y' Hy1y' z'Ry' ]; exists y'.
apply weak_taus with y1; auto.
destruct z'Ry' as [ w' ]; exists w'; auto; apply S_star with z'; auto.
apply wexpansion1_ctrl_t; auto.
unfold evolve_t; eapply evolve_incl; try apply HS; intros u v K; exists u; auto.
