Require Export Functions.
Require Export Reductions.
Set Implicit Arguments.
Section Global.
Variable A: Type.
Section Sim.
Variables X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Definition evolve_1 l R S := diagram (TX l) R (Weak TY l) S.
Definition evolve_t R S := evolve_1 (T A) R S.
Definition evolve_a R S := forall a, evolve_1 (L a) R S .
Definition evolve R S := forall l, evolve_1 l R S.
Definition simulation_t R := evolve_t R R.
Definition simulation R := evolve R R.
Definition expansion1 R := diagram_r TX R (EWeak TY) R.
Definition wexpansion1 R := diagram_r TX R (REWeak TY) R.
Variable F: function X Y.
Record monotonic: Prop := mkmon { mon_m:> increasing F; mon_t: forall R S, evolve_t R S -> incl R S -> evolve_t (F R) (F S); mon_a: forall R S, evolve R S -> incl R S -> evolve_a (F R) (F S) }.
Record wmonotonic: Prop := mkwmon { wmon_m:> increasing F; wmon_t: forall R, simulation_t R -> simulation_t (F R); wmon_a: forall R S, simulation_t R -> simulation_t S -> evolve_a R S -> incl R S -> evolve_a (F R) (F S) }.
Variable B: relation X.
Record controlled: Prop := mkctrl { ctrl_t: forall R, evolve_t R (comp (star B) R) -> simulation_t (comp (star B) R); ctrl_a: forall R S, evolve_t R (comp (star B) R) -> simulation_t S -> evolve_a R S -> incl R S -> evolve_a (comp (star B) R) (comp (star B) S) }.
End Sim.
Section Bi.
Variables X Y: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Definition bisimulation R := simulation TX TY R /\ simulation TY TX (trans R).
Definition expansion R := expansion1 TX TY R /\ simulation TY TX (trans R).
Definition wexpansion R := wexpansion1 TX TY R /\ simulation TY TX (trans R).
Definition bisim := union_st bisimulation.
Definition expand := union_st expansion.
Definition wexpand := union_st wexpansion.
End Bi.
Section Composition.
Variables X Y Z: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variable TZ: reduction_t A Z.
Variable R: relation2 X Y.
Variable S: relation2 Y Z.
Let wexpansion1_t: wexpansion1 TY TZ S -> forall x x' y, star (TY (T _)) x x' -> S x y -> exists2 y', star (TZ (T _)) y y' & S x' y'.
Proof.
intros H x x' y Hxx'; cgen y; induction Hxx' as [ x | x1 x x' Hxx1 Hx1x' IH ]; intros y xRy.
exists y; auto.
destruct (H _ _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
destruct (IH _ x1Ry1) as [ y' Hy1y' x'Ry' ].
exists y'; auto.
celim Hyy1; intro Hyy1.
destruct Hyy1; auto.
apply S_star with y1; auto.
End Composition.
Section BiComposition.
Variables X Y Z: Type.
Variable TX: reduction_t A X.
Variable TY: reduction_t A Y.
Variable TZ: reduction_t A Z.
Variable R: relation2 X Y.
Variable S: relation2 Y Z.
End BiComposition.
Section Properties.
Variable X: Type.
Variable TX: reduction_t A X.
Definition bicontrolled R := controlled TX TX R /\ incl R (bisim TX TX).
End Properties.
End Global.
Ltac union_evolve n := unfold UIter, simulation_t, evolve_t; apply union_evolve; intro n; apply evolve_union.

Lemma weak_strong_t: forall R, simulation_t R -> diagram (Weak TX (T A)) R (Weak TY (T A)) R.
Proof.
Admitted.

Lemma weak_strong: forall R, simulation R -> diagram_r (Weak TX) R (Weak TY) R.
Proof.
intros R HR; generalize (weak_strong_t (HR (T A))); intros Ht l; destruct l as [ | a ]; auto.
intros x x' y Hxx' xRy; destruct Hxx' as [ x1 Hxx1 Hx1x' ]; destruct Hx1x' as [ x2 Hx1x2 Hx2x' ].
destruct (Ht _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
destruct (HR _ _ _ _ Hx1x2 x1Ry1) as [ y2 Hy1y2 x2Ry2 ].
destruct (Ht _ _ _ Hx2x' x2Ry2) as [ y' Hy2y' x'Ry' ].
exists y'; auto.
apply taus_weak with y1; auto.
Admitted.

Lemma union2_evolve_left: forall l R S S', evolve_1 l R S -> evolve_1 l R (union2 S S').
Proof.
Admitted.

Lemma union2_evolve_right: forall l R S S', evolve_1 l R S' -> evolve_1 l R (union2 S S').
Proof.
Admitted.

Lemma union_evolve: forall l I R S, (forall i:I, evolve_1 l (R i) S) -> evolve_1 l (union R) S.
Proof.
intros l I R S H x x' y Hxx' xRy; destruct xRy as [ i xRy ].
Admitted.

Lemma evolve_union: forall l J R S, (exists j:J, evolve_1 l R (S j)) -> evolve_1 l R (union S).
Proof.
intros l J R S H x x' y Hxx' xRy.
destruct H as [ j Hj ]; destruct (Hj _ _ _ Hxx' xRy) as [ y' ].
Admitted.

Lemma incl_evolve: forall l R R' S, incl R R' -> evolve_1 l R' S -> evolve_1 l R S.
Proof.
intros l R R' S HRR' HR'S x x' y Hxx' xRy.
Admitted.

Lemma evolve_incl: forall l S R S', incl S S' -> evolve_1 l R S -> evolve_1 l R S'.
Proof.
intros l S R S' HSS' HRS x x' y Hxx' xRy.
Admitted.

Lemma simulation_eeq: forall R S, eeq R S -> simulation R -> simulation S.
Proof.
intros R S HRS H l.
apply evolve_incl with R.
apply (proj1 HRS).
apply incl_evolve with R.
apply (proj2 HRS).
Admitted.

Lemma simulation_t_eeq: forall R S, eeq R S -> simulation_t R -> simulation_t S.
Proof.
intros R S HRS H; unfold simulation_t, evolve_t.
apply evolve_incl with R.
apply (proj1 HRS).
apply incl_evolve with R.
apply (proj2 HRS).
Admitted.

Lemma bisimulation_bisim: bisimulation bisim.
Proof.
Admitted.

Lemma expansion_expand: expansion expand.
Proof.
Admitted.

Lemma union2_evolve: forall l R R' S, evolve_1 l R S -> evolve_1 l R' S -> evolve_1 l (union2 R R') S.
Proof.
intros l R R' S HR HR' x x' y Hxx' xRy; destruct xRy as [ xRy | xRy ].
destruct (HR _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto.
destruct (HR' _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto.
