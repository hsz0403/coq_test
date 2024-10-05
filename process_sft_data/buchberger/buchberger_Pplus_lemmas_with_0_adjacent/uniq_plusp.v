Require Export Peq.
Require Import Arith.
Require Import LetP.
Section Pplus.
Load hCoefStructure.
Load hOrderStructure.
Load hEq.
Inductive plusP : list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop := | nillu1 : forall l1, plusP (pO A n) l1 l1 | nillu2 : forall l1, plusP l1 (pO A n) l1 | mainu1 : forall a1 a2 l1 l2 l3, ltT ltM a2 a1 -> plusP l1 (pX a2 l2) l3 -> plusP (pX a1 l1) (pX a2 l2) (pX a1 l3) | mainu2a : forall a1 a2 l1 l2 l3, plusP l1 l2 l3 -> eqT a1 a2 -> zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a2) -> plusP (pX a1 l1) (pX a2 l2) l3 | mainu2b : forall a1 a2 l1 l2 l3, plusP l1 l2 l3 -> eqT a1 a2 -> ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a2) -> plusP (pX a1 l1) (pX a2 l2) (pX (plusTerm (A:=A) plusA (n:=n) a1 a2) l3) | mainu3 : forall a1 a2 l1 l2 l3, ltT ltM a1 a2 -> plusP (pX a1 l1) l2 l3 -> plusP (pX a1 l1) (pX a2 l2) (pX a2 l3).
Hint Resolve nillu1 nillu2 mainu1 mainu2a mainu2b mainu3 : core.
Definition projsig1 (A : Set) (P : A -> Prop) (H : sig P) := let (a, _) return A := H in a.
Definition plusp : forall l, {a : _ | plusP (fst l) (snd l) a}.
intros l; pattern l in |- *.
apply well_founded_induction with (R := lessP A n); auto.
apply wf_lessP; auto.
intros x; case x; intros p q; simpl in |- *.
case p; clear p.
intros H'; exists q; auto.
intros a1 m1; case q; clear q.
intros H'; exists (pX a1 m1); auto.
intros a2 m2 H'; case (ltT_dec A n ltM ltM_dec a1 a2); [ intros P; case P; clear P | idtac ]; intros H1.
lapply (H' (pX a1 m1, m2)); simpl in |- *; [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX a2 Orec); auto.
change (plusP (pX a1 m1) (pX a2 m2) (pX a2 Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
lapply (H' (m1, pX a2 m2)); simpl in |- *; [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX a1 Orec); auto.
change (plusP (pX a1 m1) (pX a2 m2) (pX a1 Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
apply LetP with (h := plusTerm (A:=A) plusA (n:=n) a1 a2).
intros letA eqL0; case (zeroP_dec A A0 eqA eqA_dec n letA); intros H'0.
lapply (H' (m1, m2)); simpl in |- *; [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists Orec; auto.
change (plusP (pX a1 m1) (pX a2 m2) Orec) in |- *; auto.
rewrite eqL0 in H'0; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
lapply (H' (m1, m2)); simpl in |- *; [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX letA Orec); auto.
change (plusP (pX a1 m1) (pX a2 m2) (pX letA Orec)) in |- *; auto.
rewrite eqL0; auto.
rewrite eqL0 in H'0; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
Defined.
Set Implicit Arguments.
Unset Strict Implicit.
Definition pluspf l1 l2 := projsig1 _ _ (plusp (l1, l2)).
Hint Unfold projsig1 pluspf : core.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve pluspf_is_plusP : core.
Hint Resolve eqp_refl : core.
Hint Resolve eqp_refl : core.
Hint Resolve pluspf_inv1 pluspf_inv2 pluspf_inv3a pluspf_inv3b : core.
Hint Resolve plusP_zero_pOl plusP_zero_pOr : core.
Hint Resolve eqp_trans : core.
Hint Resolve plusP_uniq_eqP : core.
Hint Resolve p0_pluspf_l p0_pluspf_r : core.
Hint Resolve plusTerm_is_pX : core.
Hint Resolve pluspf_assoc : core.
Hint Resolve eqp_pluspf_com : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition splus : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (pluspf p1 p2); auto.
apply canonical_pluspf; auto.
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
End Pplus.

Theorem uniq_plusp : forall l l3 l4, plusP (fst l) (snd l) l3 -> plusP (fst l) (snd l) l4 -> l3 = l4.
intros l; pattern l in |- *.
apply well_founded_ind with (1 := wf_lessP A n).
intros (l1, l2); simpl in |- *.
case l1; clear l1.
intros H' l3 l4 H'0; inversion_clear H'0; intros H'2; inversion_clear H'2; auto.
case l2; clear l2.
simpl in |- *; intros n0 l0 H' l3 l4 H'0 H'2; inversion H'2; inversion H'0; auto.
simpl in |- *; intros n2 l2 n1 l1 Induc l3 l4 Hl3 Hl4.
case (plusP_inv l1 l2 l4 n1 n2); auto.
intros x H'; elim H'; [ intros H'0; elim H'0; intros H'1 H'2; elim H'2; intros H'3 H'4; rewrite H'4; clear H'2 H'0 H' | intros H'0; clear H' ].
case (plusP_inv l1 l2 l3 n1 n2); auto.
intros x0 H'; elim H'; [ intros H'0; elim H'0; intros H'2 H'5; elim H'5; intros H'6 H'7; rewrite H'7; clear H'5 H'0 H' | intros H'0; clear H' ]; auto.
apply pX_inj; auto.
apply Induc with (y := (l1, n2 :: l2)); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim H'0; [ intros H'; elim H'; intros H'2 H'5; clear H' H'0 | intros H'; clear H'0 ].
absurd (ltT ltM n1 n2); auto.
elim H'; intros H'0 H'2; try exact H'0; clear H'.
absurd (eqT n2 n1); auto.
apply (eqT_sym A n n1); auto.
elim H'0; [ intros H'; elim H'; intros H'1 H'2; elim H'2; intros H'3 H'4; rewrite H'4; clear H'2 H' H'0 | intros H'; clear H'0 ].
case (plusP_inv l1 l2 l3 n1 n2); auto.
intros x0 H'; elim H'; [ intros H'0; elim H'0; intros H'2 H'5; clear H'0 H' | intros H'0; clear H' ].
absurd (ltT ltM n1 n2); auto.
elim H'0; [ intros H'; elim H'; intros H'2 H'5; elim H'5; intros H'6 H'7; rewrite H'7; clear H'5 H' H'0 | intros H'; clear H'0 ].
apply pX_inj; auto.
apply Induc with (y := (pX n1 l1, l2)); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
elim H'; intros H'0 H'2; try exact H'0; clear H'.
absurd (eqT n1 n2); auto.
elim H'; intros H'0 H'1; try exact H'0; clear H'.
case (plusP_inv l1 l2 l3 n1 n2); auto.
intros x0 H'; elim H'; [ intros H'2; elim H'2; intros H'3 H'4; try exact H'3; clear H'2 H' | intros H'2; clear H' ].
absurd (eqT n2 n1); auto.
apply (eqT_sym A n n1); auto.
elim H'2; [ intros H'; elim H'; intros H'3 H'4; try exact H'3; clear H' H'2 | intros H'; clear H'2 ].
absurd (eqT n1 n2); auto.
elim H'; intros H'2 H'3; elim H'3; [ intros H'4; elim H'4; intros H'5 H'6; try exact H'5; clear H'4 H'3 H' | intros H'4; clear H'3 H' ].
elim H'1; [ intros H'; clear H'1 | intros H'; elim H'; intros H'3 H'4; apply H'3 || elim H'3; clear H' H'1 ]; auto.
elim H'; intros H'1 H'3; clear H'.
apply Induc with (y := (l1, l2)); auto; red in |- *; simpl in |- *; auto.
simpl in |- *; auto with arith.
elim H'4; intros H' H'3; elim H'3; intros H'5 H'6; rewrite H'6; clear H'3 H'4.
elim H'1; [ intros H'3; clear H'1 | intros H'3; elim H'3; intros H'4 H'7; elim H'7; intros H'8 H'9; rewrite H'9; clear H'7 H'3 H'1 ].
elim H'3; intros H'1 H'4; try exact H'1; clear H'3.
apply H' || elim H'; try assumption.
apply pX_inj; auto.
apply Induc with (y := (l1, l2)); auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
