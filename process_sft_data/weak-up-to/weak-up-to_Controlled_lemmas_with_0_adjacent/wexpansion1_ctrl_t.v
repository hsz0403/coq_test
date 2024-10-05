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
