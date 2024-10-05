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

Lemma G_wmon: wmonotonic TX TX G.
Proof.
unfold G; apply Comp_wmon.
apply Union2_wmon.
apply monotonic_wmonotonic; apply identity_mon.
apply monotonic_wmonotonic; apply constant_mon.
apply (proj1 (bisimulation_bisim TX TX)).
apply star_wmon.
