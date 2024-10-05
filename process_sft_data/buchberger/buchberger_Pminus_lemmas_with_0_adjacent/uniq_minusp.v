Require Export Pmults.
Require Import Arith.
Require Import LetP.
Section Pminus.
Load hCoefStructure.
Load hOrderStructure.
Load hMults.
Inductive minusP : list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop := | mnillu1 : forall l1 : list (Term A n), minusP (pO A n) l1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l1) | mnillu2 : forall l1 : list (Term A n), minusP l1 (pO A n) l1 | mmainu1 : forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)), ltT ltM a2 a1 -> minusP l1 (pX a2 l2) l3 -> minusP (pX a1 l1) (pX a2 l2) (pX a1 l3) | mmainu2a : forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)), minusP l1 l2 l3 -> eqT a1 a2 -> zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a1 a2) -> minusP (pX a1 l1) (pX a2 l2) l3 | mmainu2b : forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)), minusP l1 l2 l3 -> eqT a1 a2 -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a1 a2) -> minusP (pX a1 l1) (pX a2 l2) (pX (minusTerm (A:=A) minusA (n:=n) a1 a2) l3) | mmainu3 : forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)), ltT ltM a1 a2 -> minusP (pX a1 l1) l2 l3 -> minusP (pX a1 l1) (pX a2 l2) (pX (invTerm (A:=A) invA (n:=n) a2) l3).
Hint Resolve mnillu1 mnillu2 mmainu1 mmainu2a mmainu2b mmainu3 : core.
Definition minuspp : forall l : list (Term A n) * list (Term A n), {a : list (Term A n) | minusP (fst l) (snd l) a}.
intros l; pattern l in |- *.
apply well_founded_induction with (A := (list (Term A n) * list (Term A n))%type) (R := lessP A n); auto.
apply wf_lessP; auto.
intros x; case x; intros l1 l2; simpl in |- *.
case l1.
intros H'; exists (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2); auto.
intros a1 m1; case l2.
intros H'; exists (pX a1 m1); auto.
intros a2 m2 H'; case (ltT_dec A n ltM ltM_dec a1 a2); [ intros P; case P; clear P | idtac ]; intros H1.
lapply (H' (pX a1 m1, m2)); simpl in |- *; [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX (invTerm (A:=A) invA (n:=n) a2) Orec); auto.
change (minusP (pX a1 m1) (pX a2 m2) (pX (invTerm (A:=A) invA (n:=n) a2) Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
lapply (H' (m1, pX a2 m2)); simpl in |- *; [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX a1 Orec); auto.
change (minusP (pX a1 m1) (pX a2 m2) (pX a1 Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
lapply (H' (m1, m2)); simpl in |- *; [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
apply LetP with (A := Term A n) (h := minusTerm (A:=A) minusA (n:=n) a1 a2).
intros u H'0; case (zeroP_dec A A0 eqA eqA_dec n u); intros Z0.
exists Orec; auto.
rewrite H'0 in Z0; auto.
change (minusP (pX a1 m1) (pX a2 m2) Orec) in |- *; auto.
exists (pX u Orec); auto.
rewrite H'0 in Z0; auto.
rewrite H'0; auto.
change (minusP (pX a1 m1) (pX a2 m2) (pX (minusTerm (A:=A) minusA (n:=n) a1 a2) Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
Defined.
Definition minuspf (l1 l2 : list (Term A n)) := projsig1 (list (Term A n)) _ (minuspp (l1, l2)).
Hint Unfold minuspf : core.
Hint Resolve minusTerm_zeroP minusTerm_zeroP_r : core.
Hint Resolve minuspf_is_minusP : core.
Hint Resolve invTerm_eqT_comp invTerm_T1_eqT_comp multTerm_invTerm_T1_eqT_comp : core.
Hint Resolve minuspf_is_pluspf_mults : core.
Hint Resolve pluspf_inv1 pluspf_inv2 pluspf_inv3a pluspf_inv3b : core.
Hint Resolve minuspf_inv1 minuspf_inv2 minuspf_inv3a minuspf_inv3b : core.
Hint Resolve mults_dist_minuspf : core.
Hint Resolve minuspf_pO_refl : core.
Hint Resolve minuspf_pOmults : core.
Hint Resolve order_pluspf : core.
Hint Resolve canonical_minuspf : core.
Definition inv : list (Term A n) -> Term A n -> Term A n.
intros p; case p.
intros a; exact (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a).
intros a1 p1 a; exact (invTerm (A:=A) invA (n:=n) a).
Defined.
Hint Resolve inv_prop : core.
Hint Resolve invTerm_T1_multTerm_T1 : core.
Definition sminus : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (minuspf p1 p2); auto.
Defined.
End Pminus.

Theorem uniq_minusp : forall (l : list (Term A n) * list (Term A n)) (l3 l4 : list (Term A n)), minusP (fst l) (snd l) l3 -> minusP (fst l) (snd l) l4 -> l3 = l4.
unfold pX, pX in |- *.
intros l; pattern l in |- *.
apply well_founded_ind with (1 := wf_lessP A n).
intros (l1, l2); simpl in |- *.
case l1; clear l1.
intros H' l3 l4 H'0; inversion_clear H'0; intros H'2; inversion_clear H'2; auto.
case l2; clear l2.
simpl in |- *; intros n0 l0 H' l3 l4 H'0 H'2.
inversion H'2; inversion H'0; auto.
simpl in |- *; intros n2 l2 n1 l1 Induc l3 l4 Hl3 Hl4.
case (minusP_inv l1 l2 l4 n1 n2); auto.
intros x H'; elim H'; intros H'0; [ idtac | elim H'0; clear H'0; intros H'0 ]; clear H'; (case (minusP_inv l1 l2 l3 n1 n2); auto; intros x1 H'; elim H'; intros H'1; [ idtac | elim H'1; clear H'1; intros H'1 ]; clear H').
elim H'1; intros H' H'2; elim H'2; intros H'3 H'4; rewrite H'4; clear H'2 H'1.
elim H'0; intros H'1 H'2; elim H'2; intros H'5 H'6; rewrite H'6; clear H'2 H'0.
apply pX_inj; auto.
apply Induc with (y := (l1, pX n2 l2)); auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (ltT ltM n1 n2); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n2 n1); auto.
apply (eqT_sym A n); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (ltT ltM n1 n2); auto.
elim H'1; intros H' H'2; elim H'2; intros H'3 H'4; rewrite H'4; clear H'2 H'1.
elim H'0; intros H'1 H'2; elim H'2; intros H'5 H'6; rewrite H'6; clear H'2 H'0.
apply pX_inj; auto.
apply Induc with (y := (pX n1 l1, l2)); auto; red in |- *; simpl in |- *; auto.
rewrite <- plus_n_Sm; auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n1 n2); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n2 n1); auto.
apply (eqT_sym A n); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n1 n2); auto.
elim H'1; intros H' H'2; elim H'2; [ intros H'3; clear H'2 H'1 | intros H'3; elim H'3; intros H'4 H'5; elim H'5; intros H'6 H'7; rewrite H'7; clear H'5 H'3 H'2 H'1 ].
elim H'0; intros H'1 H'2; elim H'2; [ intros H'4; clear H'2 H'0 | intros H'4; elim H'4; intros H'5 H'6; apply H'5 || elim H'5; try assumption; clear H'4 H'2 H'0 ].
elim H'4; intros H'0 H'2; clear H'4.
elim H'3; intros H'4 H'5; clear H'3.
apply Induc with (y := (l1, l2)); auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
elim H'3; intros H'0 H'2; clear H'3; auto.
elim H'0; intros H'1 H'2; elim H'2; [ intros H'3; clear H'2 H'0 | intros H'3; elim H'3; intros H'5 H'8; elim H'8; intros H'9 H'10; rewrite H'10; clear H'8 H'3 H'2 H'0 ].
elim H'3; intros H'0 H'2; clear H'3.
apply H'4 || elim H'4; auto.
apply pX_inj; auto.
apply Induc with (y := (l1, l2)); auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
