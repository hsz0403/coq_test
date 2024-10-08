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

Lemma union2_evolve: forall l R R' S, evolve_1 l R S -> evolve_1 l R' S -> evolve_1 l (union2 R R') S.
Proof.
intros l R R' S HR HR' x x' y Hxx' xRy; destruct xRy as [ xRy | xRy ].
destruct (HR _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto.
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

Lemma wexpansion_wexpand: wexpansion wexpand.
Proof.
Admitted.

Lemma wexpand_bisim: incl wexpand bisim.
Proof.
intros P Q H; destruct H as [ R H H' ]; exists R; auto; split.
intros l x x' y Hxx' xRy; destruct (proj1 H _ _ _ _ Hxx' xRy) as [ y' Hyy' x'Ry' ]; exists y'; auto.
destruct l; simpl in Hyy'.
celim Hyy'; intro Hyy'; try destruct Hyy'; auto.
exists y; auto.
Admitted.

Lemma simulation_comp: simulation TX TY R -> simulation TY TZ S -> simulation TX TZ (comp R S).
Proof.
intros HR HS l x x' y Hxx' xRy; destruct xRy as [ t xRt tRy ].
destruct (HR _ _ _ _ Hxx' xRt) as [ t' Htt' x'Rt' ].
destruct (weak_strong HS _ _ _ _ Htt' tRy) as [ y' Hyy' t'Ry' ].
Admitted.

Lemma expansion1_comp: expansion1 TX TY R -> expansion1 TY TZ S -> expansion1 TX TZ (comp R S).
Proof.
intros HR HS l x x' y Hxx' xRy; destruct xRy as [ t xRt tRy ].
destruct (HR _ _ _ _ Hxx' xRt) as [ t' Htt' x'Rt' ]; destruct l.
celim Htt'; intro Htt'.
destruct Htt'; exists y; [ left | exists t ]; auto.
destruct (HS _ _ _ _ Htt' tRy) as [ y' Hyy' t'Ry' ]; exists y'; auto; exists t'; auto.
Admitted.

Let wexpansion1_t: wexpansion1 TY TZ S -> forall x x' y, star (TY (T _)) x x' -> S x y -> exists2 y', star (TZ (T _)) y y' & S x' y'.
Proof.
intros H x x' y Hxx'; cgen y; induction Hxx' as [ x | x1 x x' Hxx1 Hx1x' IH ]; intros y xRy.
exists y; auto.
destruct (H _ _ _ _ Hxx1 xRy) as [ y1 Hyy1 x1Ry1 ].
destruct (IH _ x1Ry1) as [ y' Hy1y' x'Ry' ].
exists y'; auto.
celim Hyy1; intro Hyy1.
destruct Hyy1; auto.
Admitted.

Lemma wexpansion1_comp: wexpansion1 TX TY R -> wexpansion1 TY TZ S -> wexpansion1 TX TZ (comp R S).
Proof.
intros HR HS l x x' y Hxx' xRy; destruct xRy as [ t xRt tRy ].
destruct (HR _ _ _ _ Hxx' xRt) as [ t' Htt' x'Rt' ]; destruct l.
celim Htt'; intro Htt'.
destruct Htt'; exists y; [ left | exists t ]; auto.
destruct (HS _ _ _ _ Htt' tRy) as [ y' Hyy' t'Ry' ]; exists y'; auto; exists t'; auto.
destruct Htt' as [ t1 Htt1 Ht1t' ].
destruct (HS _ _ _ _ Htt1 tRy) as [ y1 Hyy1 t1Ry1 ].
destruct (wexpansion1_t HS Ht1t' t1Ry1) as [ y' Hy1y' t'Ry' ].
exists y'.
destruct Hyy1 as [ y2 ]; exists y2; auto; apply star_trans with y1; auto.
Admitted.

Lemma bisimulation_comp: bisimulation TX TY R -> bisimulation TY TZ S -> bisimulation TX TZ (comp R S).
Proof.
unfold bisimulation; intros HR HS; split.
apply simulation_comp with TY; intuition.
eapply simulation_eeq; try (apply eeq_sym; apply inv_comp).
Admitted.

Lemma expansion_comp: expansion TX TY R -> expansion TY TZ S -> expansion TX TZ (comp R S).
Proof.
unfold expansion; intros HR HS; split.
apply expansion1_comp with TY; intuition.
eapply simulation_eeq; try (apply eeq_sym; apply inv_comp).
Admitted.

Lemma wexpansion_comp: wexpansion TX TY R -> wexpansion TY TZ S -> wexpansion TX TZ (comp R S).
Proof.
unfold wexpansion; intros HR HS; split.
apply wexpansion1_comp with TY; intuition.
eapply simulation_eeq; try (apply eeq_sym; apply inv_comp).
Admitted.

Lemma bisim_sym: symmetric (bisim TX TX).
Proof.
intros x y H; destruct H as [ R HR H ].
exists (trans R); auto.
Admitted.

Lemma bisim_refl: reflexive (bisim TX TX).
Proof.
intro u; exists (eq (A:=X)); auto.
Admitted.

Lemma bisim_trans: transitive (bisim TX TX).
Proof.
intros y x z XY YZ.
destruct XY as [ R HR XY ].
destruct YZ as [ S HS YZ ].
exists (comp R S).
apply bisimulation_comp with TX; auto.
Admitted.

Lemma expand_refl: reflexive (expand TX TX).
Proof.
intro u; exists (eq (A:=X)); auto.
split; intros l x x' y Hxx' xRy; exists x'; destruct xRy; auto.
Admitted.

Lemma expand_trans: transitive (expand TX TX).
Proof.
intros y x z XY YZ.
destruct XY as [ R HR XY ].
destruct YZ as [ S HS YZ ].
exists (comp R S).
apply expansion_comp with TX; auto.
Admitted.

Lemma wexpand_refl: reflexive (wexpand TX TX).
Proof.
intro u; exists (eq (A:=X)); auto.
split; intros l x x' y Hxx' xRy; exists x'; destruct xRy; auto.
Admitted.

Lemma wexpand_trans: transitive (wexpand TX TX).
Proof.
intros y x z XY YZ.
destruct XY as [ R HR XY ].
destruct YZ as [ S HS YZ ].
exists (comp R S).
apply wexpansion_comp with TX; auto.
Admitted.

Lemma expand_wexpand: incl expand wexpand.
Proof.
intros P Q H; destruct H as [ R H H' ]; exists R; auto; split.
intros l x x' y Hxx' xRy; destruct (proj1 H _ _ _ _ Hxx' xRy) as [ y' Hyy' x'Ry' ]; exists y'; auto.
destruct l; simpl in Hyy'; intuition; exists y'; auto.
exact (proj2 H).
