Require Export Diagrams.
Set Implicit Arguments.
Ltac cgen H := generalize H; clear H.
Section Reductions.
Section R.
Variables A X: Type.
Definition reduction := A -> relation X.
Definition incl_r: relation reduction := fun R1 R2 => forall a, incl (R1 a) (R2 a).
Definition eeq_r: relation reduction := fun R1 R2 => forall a, eeq (R1 a) (R2 a).
End R.
Variable A: Type.
Section Diagram.
Variables X Y: Type.
Definition diagram_r(RX: reduction A X) R (RY: reduction A Y) S := forall a, diagram (RX a) R (RY a) S.
End Diagram.
Section Weak.
Inductive Lbl: Type := T | L(a: A).
Definition reduction_t := reduction Lbl.
Variable X: Type.
Variable Red: reduction_t X.
Definition Weak: reduction_t X := fun l => match l with | T => star (Red T) | L a => comp (star (Red T)) (comp (Red (L a)) (star (Red T))) end.
Definition EWeak: reduction_t X := fun l => match l with | T => union2 (eq (A:=X)) (Red T) | L a => Red (L a) end.
Definition REWeak: reduction_t X := fun l => match l with | T => union2 (eq (A:=X)) (Red T) | L a => comp (Red (L a)) (star (Red T)) end.
Hint Immediate weak_refl.
End Weak.
End Reductions.
Hint Immediate weak_refl.
Hint Resolve red_weak.

Theorem Weak_ind: forall P: Lbl -> X -> X -> Prop, (forall x, P T x x) -> (forall y l x z , Red T x y -> Weak l y z -> P l y z -> P l x z) -> (forall y a x z, Red (L a) x y -> Weak T y z -> P T y z -> P (L a) x z) -> forall l x x', Weak l x x' -> P l x x'.
Proof.
intros P Hrefl Htau Ha l x x' Hxx'.
destruct l.
induction Hxx' as [ x | x1 x x' Hxx1 Hx1x' IH ]; [ apply Hrefl | apply Htau with x1; assumption ].
destruct Hxx' as [ x1 Hxx1 Hx1x' ].
destruct Hx1x' as [ x2 Hx1x2 Hx2x' ].
induction Hxx1 as [ x | w x x1 Hxw Hwx1 IH ].
apply Ha with x2; simpl; auto.
clear Hx1x2.
induction Hx2x' as [ x2 | u x2 x' Hux1 Hx1x' IH ]; [ apply Hrefl | apply Htau with u; assumption ].
apply Htau with w; auto.
exists x1; auto; exists x2; assumption.
