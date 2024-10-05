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

Lemma taus_weak: forall y l x z, Weak T x y -> Weak l y z -> Weak l x z.
Proof.
intros y l; destruct l; simpl; intros x z XY YZ.
apply star_trans with y; assumption.
destruct YZ as [ w YW WZ ].
exists w; auto.
apply star_trans with y; assumption.
