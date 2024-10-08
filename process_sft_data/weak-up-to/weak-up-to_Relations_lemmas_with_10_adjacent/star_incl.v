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

Lemma trans_incl: incl R R' -> incl (trans R) (trans R').
Proof.
Admitted.

Lemma trans_eeq: eeq R R' -> eeq (trans R) (trans R').
Proof.
Admitted.

Lemma comp_incl: incl R R' -> incl S S' -> incl (comp R S) (comp R' S').
Proof.
unfold eeq, comp, incl; intuition.
Admitted.

Lemma comp_eeq: eeq R R' -> eeq S S' -> eeq (comp R S) (comp R' S').
Proof.
Admitted.

Lemma union_incl: (forall i, incl (F i) (F' i)) -> incl (union F) (union F').
Proof.
unfold eeq, union, incl; intuition.
Admitted.

Lemma union_eeq: (forall i, eeq (F i) (F' i)) -> eeq (union F) (union F').
Proof.
Admitted.

Lemma union2_incl: incl R R' -> incl R1 R1' -> incl (union2 R R1) (union2 R' R1').
Proof.
Admitted.

Lemma union2_eeq: eeq R R' -> eeq R1 R1' -> eeq (union2 R R1) (union2 R' R1').
Proof.
Admitted.

Lemma star_eeq: eeq T T' -> eeq (star T) (star T').
Proof.
Admitted.

Lemma plus_incl: incl T T' -> incl (plus T) (plus T').
Proof.
intros H x y XY; destruct XY as [ w XW WY ]; exists w; auto.
Admitted.

Lemma plus_eeq: eeq T T' -> eeq (plus T) (plus T').
Proof.
intro H; elim H; intros H1 H2; split; intros x y XY; destruct XY as [ w XW WY ]; exists w; auto.
apply (proj1 (star_eeq H)); assumption.
Admitted.

Lemma incl_trans: incl R S -> incl S T -> incl R T.
Proof.
Admitted.

Lemma eeq_refl: eeq R R.
Proof.
Admitted.

Lemma eeq_trans: eeq R S -> eeq S T -> eeq R T.
Proof.
Admitted.

Lemma eeq_sym: eeq R S -> eeq S R.
Proof.
Admitted.

Lemma star1: forall x y, R x y -> star R x y.
Proof.
Admitted.

Lemma star_S: forall x y z, star R x y -> R y z -> star R x z.
Proof.
intros x y z XY YZ; induction XY.
apply star1; assumption.
Admitted.

Lemma star_trans: forall x y z, star R x y -> star R y z -> star R x z.
Proof.
intros x y z xy; induction xy; intuition.
Admitted.

Lemma star_incl: incl T T' -> incl (star T) (star T').
Proof.
intros H x y XY; induction XY as [ x | w x y XW WY IH ]; auto; apply S_star with w; auto.
