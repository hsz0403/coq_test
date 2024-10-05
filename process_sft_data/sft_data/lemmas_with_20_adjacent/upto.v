Require Export Settings.
Require Import Theory.
Set Implicit Arguments.
Section Modular.
Variables A X: Type.
Variable TX: reduction_t A X.
Let F := Comp (chaining_l (expand TX TX)) (chaining_r (bisim TX TX)).
Let G := Comp (star (X:=X)) (Union2 (identity (X:=X) (Y:=X)) (constant (bisim TX TX))).
Variable R: relation X.
Hypothesis HRt: evolve_t TX TX R (F R).
Hypothesis HRa: evolve_a TX TX R (G R).
Hypothesis HRt': evolve_t TX TX (trans R) (F (trans R)).
Hypothesis HRa': evolve_a TX TX (trans R) (G (trans R)).
End Modular.
Section Controlled.
Variables A X: Type.
Variable TX: reduction_t A X.
Variables B B': relation X.
Hypothesis HB: bicontrolled TX B.
Hypothesis HB': bicontrolled TX B'.
Let F := chaining_r (X:=X) (bisim TX TX).
Let G := Comp (star (X:=X)) (Union2 (identity (X:=X) (Y:=X)) (constant (bisim TX TX))).
Let F_mon: monotonic TX TX F.
Proof.
unfold F; apply chaining_r_mon; apply (proj1 (bisimulation_bisim TX TX)).
Let FG: contains F G.
Proof.
intros R x y XY; destruct XY as [ w XW WY ].
unfold G, Comp, Union2; simpl; apply S_star with w; auto.
left; auto.
apply star1; right; auto.
Let BG: contains (chaining_l (star B)) G.
Proof.
intros R x y XY; destruct XY as [ w XW WY ].
unfold G, Comp, Union2, constant; simpl; apply S_star with w; auto.
right; induction XW as [ w | z x w ZX XW IH ].
apply bisim_refl.
apply bisim_trans with z; auto.
apply (proj2 HB _ _ ZX).
apply star1; left; auto.
Let B'G: contains (chaining_l (star B')) G.
Proof.
intros R x y XY; destruct XY as [ w XW WY ].
unfold G, Comp, Union2, constant; simpl; apply S_star with w; auto.
right; induction XW as [ w | z x w ZX XW IH ].
apply bisim_refl.
apply bisim_trans with z; auto.
apply (proj2 HB' _ _ ZX).
apply star1; left; auto.
Variable R: relation X.
Hypothesis HRt: evolve_t TX TX R (comp (star B) (F R)).
Hypothesis HRa: evolve_a TX TX R (G R).
Hypothesis HRt': evolve_t TX TX (trans R) (comp (star B') (F (trans R))).
Hypothesis HRa': evolve_a TX TX (trans R) (G (trans R)).
End Controlled.

Lemma F_mon: monotonic TX TX F.
Proof.
unfold F; apply Comp_mon.
apply chaining_r_mon.
apply (proj1 (bisimulation_bisim TX TX)).
apply chaining_l_mon.
Admitted.

Lemma G_wmon: wmonotonic TX TX G.
Proof.
unfold G; apply Comp_wmon.
apply Union2_wmon.
apply monotonic_wmonotonic; apply identity_mon.
apply monotonic_wmonotonic; apply constant_mon.
apply (proj1 (bisimulation_bisim TX TX)).
Admitted.

Lemma FG: contains F G.
Proof.
intros R x y XY; destruct XY as [ x' XX' X'Y ]; destruct X'Y as [ y' X'Y' Y'Y ].
unfold G, Comp, Union2; simpl; apply S_star with x'; auto.
right; unfold constant; apply wexpand_bisim; apply expand_wexpand; auto.
apply S_star with y'.
left; auto.
Admitted.

Lemma G_reverse: forall R, eeq (trans (G R)) (G (trans R)).
intros R; unfold G, Comp, Union2, identity, constant.
eapply eeq_trans; [ apply inv_star | apply star_eeq ].
eapply eeq_trans; [ apply inv_union2 | apply union2_eeq; auto ].
Admitted.

Let F_mon: monotonic TX TX F.
Proof.
Admitted.

Let FG: contains F G.
Proof.
intros R x y XY; destruct XY as [ w XW WY ].
unfold G, Comp, Union2; simpl; apply S_star with w; auto.
left; auto.
Admitted.

Let BG: contains (chaining_l (star B)) G.
Proof.
intros R x y XY; destruct XY as [ w XW WY ].
unfold G, Comp, Union2, constant; simpl; apply S_star with w; auto.
right; induction XW as [ w | z x w ZX XW IH ].
apply bisim_refl.
apply bisim_trans with z; auto.
apply (proj2 HB _ _ ZX).
Admitted.

Let B'G: contains (chaining_l (star B')) G.
Proof.
intros R x y XY; destruct XY as [ w XW WY ].
unfold G, Comp, Union2, constant; simpl; apply S_star with w; auto.
right; induction XW as [ w | z x w ZX XW IH ].
apply bisim_refl.
apply bisim_trans with z; auto.
apply (proj2 HB' _ _ ZX).
Admitted.

Theorem upto_ctrl: incl R (bisim TX TX).
Proof.
intros x y H; exists (UIter (UIter G) R).
split.
apply controlled_correct with B F; auto.
exact (proj1 HB).
unfold G; apply G_wmon.
unfold transparent, F, chaining_r; intro U; apply (proj1 (comp_assoc (star B) U (bisim TX TX))).
apply simulation_eeq with (UIter (UIter G) (trans R)).
unfold G; apply eeq_sym; repeat apply UIter_trans; repeat apply UIter_inc; try apply (wmon_m (G_wmon TX)).
apply G_reverse.
apply controlled_correct with B' F; auto.
exact (proj1 HB').
unfold G; apply G_wmon.
unfold transparent, F, chaining_r; intro U; apply (proj1 (comp_assoc (star B') U (bisim TX TX))).
Admitted.

Theorem upto: incl R (bisim TX TX).
Proof.
intros x y H; exists (UIter (UIter G) R).
split.
apply unified_correct with F; auto.
exact F_mon.
exact G_wmon.
exact FG.
apply simulation_eeq with (UIter (UIter G) (trans R)).
apply eeq_sym; repeat apply UIter_trans; repeat apply UIter_inc; try apply (wmon_m G_wmon).
apply G_reverse.
apply unified_correct with F; auto.
exact F_mon.
exact G_wmon.
exact FG.
exists 0; exact H.
