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

Lemma identity_mon: monotonic TX TY (identity (X:=X) (Y:=Y)).
Proof.
Admitted.

Lemma constant_mon: simulation TX TY R -> monotonic TX TY (constant R).
Proof.
intro H; apply mkmon; intros; unfold constant, evolve_t, evolve_a; auto.
Admitted.

Lemma chaining_r_mon: simulation TY TY T -> monotonic TX TY (chaining_r T).
Proof.
intro H; apply mkmon; unfold chaining_r; intros U V HUV.
intros x y L; destruct L as [ w ]; exists w; auto.
intros HUV' x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ]; destruct (HUV _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ]; destruct (weak_strong H _ _ _ _ Hww' wRy) as [ y' Hyy' w'Ry' ].
exists y'; auto; exists w'; auto.
intros HUV' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ]; destruct (HUV _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ]; destruct (weak_strong H _ _ _ _ Hww' wRy) as [ y' Hyy' w'Ry' ].
Admitted.

Lemma chaining_l_mon: expansion1 TX TX E -> monotonic TX TY (chaining_l E).
Proof.
clear R.
intro HS; split.
intros R S H x y XY; destruct XY as [ w XW WY ]; exists w; auto.
intros R S H H' x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
destruct (HS _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
celim Hww'; intro Hww'.
exists y; auto; exists w'; auto; destruct Hww'; apply H'; auto.
destruct (H _ _ _ Hww' wRy) as [ y' Hyy' w'Ry' ]; exists y'; auto; exists w'; auto.
intros R S H H' a x x' y Hxx' xRy; destruct xRy as [ w xRw wRy ].
destruct (HS _ _ _ _ Hxx' xRw) as [ w' Hww' x'Rw' ].
Admitted.

Lemma Comp_mon: monotonic TX TY (Comp G F).
Proof.
unfold Comp; split.
intros R S HRS; apply (mon_m HG (mon_m HF HRS)).
intros R S H H'; apply (mon_t HG (mon_t HF H H') (mon_m HF H')).
intros R S H H'; apply (mon_a HG).
intro l; destruct l.
apply (mon_t HF (H _) H').
apply (mon_a HF H H').
Admitted.

Lemma Union2_mon: monotonic TX TY (Union2 F G).
Proof.
unfold Union2; split.
intros R S HRS x y H; destruct H; [ left; apply (mon_m HF HRS) | right; apply (mon_m HG HRS) ]; auto.
intros R S H H' x x' y Hxx' xRy; celim xRy; intro xRy; [ destruct (mon_t HF H H' _ _ _ Hxx' xRy) as [ y' ] | destruct (mon_t HG H H' _ _ _ Hxx' xRy) as [ y' ] ]; exists y'; auto; [ left | right ]; auto.
Admitted.

Lemma UExp_mon: forall n, monotonic TX TY (fun R => UExp F R n).
Proof.
intro n; induction n as [ | n IH ].
apply (identity_mon TX TY).
simpl; fold (Union2 (fun R => UExp F R n) (fun R => F (UExp F R n))).
apply Union2_mon; auto.
fold (Comp F (fun R => UExp F R n)).
Admitted.

Lemma UIter_mon: monotonic TX TY (UIter F).
Proof.
unfold UIter.
change (fun R => union (UExp F R)) with (Union (fun n => (fun R => UExp F R n))).
Admitted.

Lemma Union_mon: monotonic TX TY (Union H).
Proof.
unfold Union; split.
intros R S HRS x y K; destruct K as [ i ]; exists i; apply (mon_m (HH i) HRS); auto.
intros R S HR HR' x x' y Hxx' xRy; destruct xRy as [ i xRy ]; destruct (mon_t (HH i) HR HR' _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto; exists i; auto.
intros R S HR HR' a x x' y Hxx' xRy; destruct xRy as [ i xRy ]; destruct (mon_a (HH i) HR HR' _ _ _ _ Hxx' xRy) as [ y' ]; exists y'; auto; exists i; auto.
