Set Implicit Arguments.
Ltac cgen H := generalize H; clear H.
Ltac celim H := elim H; clear H.
Definition relation2(X Y: Type) := X -> Y -> Prop.
Definition relation (X: Type) := relation2 X X.
Definition set(X: Type) := X -> Prop.
Section Definitions.
Variables X Y Z: Type.
Definition incl: relation (relation2 X Y) := fun R1 R2 => forall x y, R1 x y -> R2 x y.
Definition eeq: relation (relation2 X Y) := fun R1 R2 => incl R1 R2 /\ incl R2 R1.
Variable R: relation X.
Definition reflexive := forall x, R x x.
Definition transitive := forall y x z, R x y -> R y z -> R x z.
Definition symmetric := forall x y, R x y -> R y x.
Definition antisymmetric := forall x y, R x y -> R y x -> x=y.
End Definitions.
Hint Unfold incl.
Section Operators.
Section O.
Variables X Y Z: Type.
Variable Rxy: relation2 X Y.
Variable Rxy': relation2 X Y.
Variable Ryz: relation2 Y Z.
Definition eta2: relation2 X Y := fun x y => Rxy x y.
Definition trans: relation2 Y X := fun y x => Rxy x y.
Definition comp: relation2 X Z := fun x z => exists2 y, Rxy x y & Ryz y z.
Definition union2: relation2 X Y := fun x y => Rxy x y \/ Rxy' x y.
Definition union (I: Type) R: relation2 X Y := fun x y => exists i: I, R i x y.
Definition union_st (P: set (relation2 X Y)) := fun x y => exists2 R, P R & R x y.
End O.
Variable X: Type.
Variable R: relation X.
Inductive star: relation X := | star_refl: forall x, star x x | S_star: forall y x z, R x y -> star y z -> star x z.
Definition plus: relation X := comp R star.
End Operators.
Hint Unfold trans.
Hint Immediate star_refl.
Section Eeq1.
Variables I X Y Z: Type.
Variable R' R1': relation2 X Y.
Variable S': relation2 Y Z.
Variable R R1: relation2 X Y.
Variable S : relation2 Y Z.
Variables T' T: relation X.
Variables F' F: I -> relation2 X Y.
End Eeq1.
Hint Resolve trans_incl.
Hint Resolve comp_incl.
Hint Resolve union_incl.
Hint Resolve star_incl.
Hint Resolve plus_incl.
Hint Resolve trans_eeq.
Hint Resolve comp_eeq.
Hint Resolve union_eeq.
Hint Resolve star_eeq.
Hint Resolve plus_eeq.
Section InclEeq.
Variables X Y: Type.
Variables S R T: relation2 X Y.
End InclEeq.
Hint Immediate incl_refl.
Hint Immediate eeq_refl.
Hint Resolve eeq_sym.
Section star.
Variable X: Type.
Variable R: relation X.
End star.
Hint Resolve star1.
Hint Resolve plus1.
Hint Resolve plus_star.
Ltac destar H w := match type of H with star _ ?x ?y => destruct H as [ x | w x y _H1 _H2 ]; [ idtac | generalize (S_plus _ _H1 _H2); clear _H1 _H2; intro H ] | _ => fail "not a star hypothesis" end.
Section Plus_WF.
Variable X: Set.
Variable R: relation X.
Hypothesis Rwf: well_founded (trans R).
Hint Resolve Acc_clos_trans.
End Plus_WF.
Section Eeq2.
Variables I X Y Z: Type.
Variables R R': relation2 X Y.
Variable S: relation2 Y Z.
Variable T: relation X.
Variable F: I -> relation2 X Y.
End Eeq2.
Hint Immediate inv_inv.
Hint Immediate inv_comp.
Hint Immediate inv_union.
Hint Immediate inv_star.
Hint Immediate inv_plus.
Hint Immediate comp_assoc.
Hint Immediate comp_star_star.
Hint Immediate comp_plus_star.
Hint Immediate comp_star_plus.

Lemma eeq_refl: eeq R R.
Proof.
intros; split; apply incl_refl.
