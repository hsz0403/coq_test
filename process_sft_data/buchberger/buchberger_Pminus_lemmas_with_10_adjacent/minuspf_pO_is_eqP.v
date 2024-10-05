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
Admitted.

Theorem zerop_is_eqTerm : forall a b : Term A n, eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> eqTerm (A:=A) eqA (n:=n) a b.
intros a b H' H'0.
cut (eqT a (invTerm (A:=A) invA (n:=n) b)); [ intros eq1 | idtac ].
cut (eqT a (plusTerm (A:=A) plusA (n:=n) b (invTerm (A:=A) invA (n:=n) b))); [ intros eq2 | idtac ].
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a (plusTerm (A:=A) plusA (n:=n) b (invTerm (A:=A) invA (n:=n) b))); auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply plusTerm_invTerm_zeroP with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a (plusTerm (A:=A) plusA (n:=n) (invTerm (A:=A) invA (n:=n) b) b)); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply (eqT_trans A n) with (plusTerm plusA b (invTerm invA b)); auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply plusTerm_com with (1 := cs); auto.
apply plusTerm_com with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)) b); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply plusTerm_assoc with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply zeroP_plusTerml with (1 := cs); auto.
apply (eqT_trans A n) with (invTerm invA b); auto.
apply plusTerm_eqT2; auto.
apply (eqT_sym A n); apply invTerm_eqT; auto.
apply zeroP_comp_eqTerm with (1 := cs) (2 := H'0).
apply eqTerm_minusTerm_plusTerm_invTerm with (1 := cs); auto.
apply (eqT_trans A n) with (1 := eq1); auto.
apply (eqT_sym A n); apply plusTerm_eqT2; auto.
Admitted.

Theorem minusTerm_zeroP_r : forall a b : Term A n, zeroP (A:=A) A0 eqA (n:=n) a -> eqT a b -> eqTerm (A:=A) eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) (invTerm (A:=A) invA (n:=n) b).
intros a b H' H0; apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply zeroP_plusTerml with (1 := cs); auto.
Admitted.

Theorem minusTerm_zeroP : forall a b : Term A n, eqT a b -> zeroP (A:=A) A0 eqA (n:=n) b -> eqTerm (A:=A) eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) a.
intros a b H' H'0.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply (eqT_trans A n) with (y := b); auto.
Admitted.

Theorem minusP_pO_is_eqP : forall p q r : list (Term A n), minusP p q r -> eqP A eqA n r (pO A n) -> eqP A eqA n p q.
intros p q r H'; elim H'; auto.
intros l1; case l1; simpl in |- *; auto.
intros t l H; inversion H.
intros a1 a2 l1 l2 l3 H H0 H1 H2; inversion H2.
intros a1 a2 l1 l2 l3 H H0 H1 H2 H3.
apply eqpP1; auto.
apply zerop_is_eqTerm; auto.
intros a1 a2 l1 l2 l3 H H0 H1 H2 H3; inversion H3.
Admitted.

Lemma minusP_inv : forall (p q l : list (Term A n)) (a b : Term A n), minusP (pX a p) (pX b q) l -> exists l1 : list (Term A n), ltT ltM b a /\ minusP p (pX b q) l1 /\ l = pX a l1 \/ ltT ltM a b /\ minusP (pX a p) q l1 /\ l = pX (invTerm (A:=A) invA (n:=n) b) l1 \/ eqT a b /\ (zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) /\ minusP p q l \/ ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) /\ minusP p q l1 /\ l = pX (minusTerm (A:=A) minusA (n:=n) a b) l1).
intros p q l a b H'; simple inversion H'.
discriminate H.
discriminate H0.
rewrite <- H3; rewrite (pX_invl A n a2 b l2 q H2); rewrite (pX_invr A n l2 q a2 b H2); rewrite (pX_invl A n a1 a l1 p H1); rewrite (pX_invr A n l1 p a1 a H1).
intros H'0 H'1; exists l3; left; split; [ idtac | split ]; auto.
rewrite <- H4.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- (pX_invl A n a2 b l2 q); try rewrite <- (pX_invl A n a1 a l1 p); auto.
rewrite <- (pX_invr A n l2 q a2 b); try rewrite <- (pX_invr A n l1 p a1 a); auto.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- H4.
rewrite <- (pX_invl A n a2 b l2 q); try rewrite <- (pX_invl A n a1 a l1 p); auto.
rewrite <- (pX_invr A n l2 q a2 b); try rewrite <- (pX_invr A n l1 p a1 a); auto.
intros H'0 H'1; exists l3; right; left.
rewrite <- (pX_invl A n a2 b l2 q); try rewrite <- (pX_invl A n a1 a l1 p); auto.
Admitted.

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
Admitted.

Theorem minuspf_is_minusP : forall l1 l2 : list (Term A n), minusP l1 l2 (minuspf l1 l2).
intros l1 l2; try assumption.
Admitted.

Theorem order_minusP : forall (l1 l2 l3 : list (Term A n)) (a : Term A n), minusP l1 l2 l3 -> canonical A0 eqA ltM (pX a l1) -> canonical A0 eqA ltM (pX a l2) -> canonical A0 eqA ltM l3 -> canonical A0 eqA ltM (pX a l3).
intros l1 l2 l3 a H'; elim H'; auto.
intros l4 H'0 H'1 H'2.
cut (canonical A0 eqA ltM l4); try apply canonical_imp_canonical with (a := a); auto; intros C0.
apply canonical_pX_eqT with (a := multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (pX a l4))) in |- *; auto.
apply (eqT_sym A n); apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a); auto.
apply (T1_eqT A A1 eqA); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply canonical_cons; auto.
apply (canonical_pX_order A A0 eqA) with (ltM := ltM) (l := l4); auto.
apply canonical_nzeroP with (ltM := ltM) (p := pX a1 l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5 H'6.
apply H'1; auto.
apply canonical_skip_fst with (b := a1); auto.
apply canonical_skip_fst with (b := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5 H'6.
apply canonical_cons; auto.
apply minusTerm_ltT_l; auto.
apply (canonical_pX_order A A0 eqA) with (l := l4); auto.
apply canonical_nzeroP with (ltM := ltM) (p := pX a1 l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply canonical_cons; auto.
apply invTerm_ltT_l; auto.
apply (canonical_pX_order A A0 eqA) with (l := l5); auto.
Admitted.

Theorem canonical_minusP : forall l1 l2 l3 : list (Term A n), minusP l1 l2 l3 -> canonical A0 eqA ltM l1 -> canonical A0 eqA ltM l2 -> canonical A0 eqA ltM l3.
intros l1 l2 l3 H'; elim H'; auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4.
apply order_minusP with (l1 := l4) (l2 := pX a2 l5); auto.
apply canonical_cons; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l4); auto.
apply H'2; auto.
apply canonical_imp_canonical with (a := a1); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply H'1; auto.
apply canonical_imp_canonical with (a := a1); auto.
apply canonical_imp_canonical with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply order_minusP with (l1 := l4) (l2 := l5); auto.
apply canonical_pX_eqT with (a := a1); auto.
apply (eqT_sym A n); apply minusTerm_eqT; auto.
apply canonical_pX_eqT with (a := a2); auto.
apply (eqT_trans A n) with (y := a1); apply (eqT_sym A n); auto.
apply minusTerm_eqT; auto.
apply H'1.
apply canonical_imp_canonical with (a := a1); auto.
apply canonical_imp_canonical with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4.
apply order_minusP with (l1 := pX a1 l4) (l2 := l5); auto.
apply canonical_pX_eqT with (a := a2); auto.
apply canonical_cons; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l5); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l5); auto.
apply canonical_pX_eqT with (a := a2); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l5); auto.
apply H'2; auto.
Admitted.

Theorem canonical_minuspf : forall l1 l2 : list (Term A n), canonical A0 eqA ltM l1 -> canonical A0 eqA ltM l2 -> canonical A0 eqA ltM (minuspf l1 l2).
intros l1 l2 H' H'0; generalize (minuspf_is_minusP l1 l2); intros u1.
Admitted.

Lemma invTerm_eqT_comp : forall a b : Term A n, eqT a b -> eqT a (invTerm (A:=A) invA (n:=n) b).
intros a b H'.
Admitted.

Lemma invTerm_T1_eqT_comp : forall a b : Term A n, eqT a b -> eqT a (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) b)).
intros a b H'.
apply (eqT_trans A n) with (y := b); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) b); auto.
Admitted.

Lemma multTerm_invTerm_T1_eqT_comp : forall a b : Term A n, eqT a b -> eqT a (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) b).
intros a b H'.
apply (eqT_trans A n) with (y := b); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) b); auto.
Admitted.

Lemma minusP_is_plusP_mults : forall p q r : list (Term A n), minusP p q r -> eqP A eqA n r (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
intros p q r H'; elim H'; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
simpl in |- *; intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a1 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l1 (pX (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2)))); auto.
simpl in |- *; apply pluspf_inv1 with (1 := cs); auto.
change (ltT ltM (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2) a1) in |- *.
apply eqT_compat_ltTl with (b := a2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2)); auto.
simpl in |- *; apply pluspf_inv3a with (1 := cs); auto.
change (eqT a1 (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2)) in |- *.
apply (eqT_trans A n) with (y := a2); auto.
change (zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2))) in |- *; auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := minusTerm (A:=A) minusA (n:=n) a1 a2); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a1 (invTerm (A:=A) invA (n:=n) a2)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); auto.
apply eqTerm_invTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX (plusTerm (A:=A) plusA (n:=n) a1 (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2)) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2))); auto.
apply eqpP1; auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a1 (invTerm (A:=A) invA (n:=n) a2)); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
simpl in |- *; apply pluspf_inv3b with (1 := cs); auto.
change (eqT a1 (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2)) in |- *.
apply (eqT_trans A n) with (y := a2); auto.
change (~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2))) in |- *; auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := minusTerm (A:=A) minusA (n:=n) a1 a2); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a1 (invTerm (A:=A) invA (n:=n) a2)); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX a1 l1) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2))); auto.
apply eqpP1; auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
simpl in |- *; apply pluspf_inv2 with (1 := cs); auto.
change (ltT ltM a1 (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2)) in |- *; auto.
Admitted.

Theorem minuspf_is_pluspf_mults : forall p q : list (Term A n), eqP A eqA n (minuspf p q) (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
intros p q; try assumption.
Admitted.

Theorem pO_minusP_inv1 : forall p q : list (Term A n), minusP (pO A n) p q -> q = mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p.
intros p; elim p.
intros q H'; inversion H'; auto.
Admitted.

Theorem pO_minusP_inv2 : forall p q : list (Term A n), minusP p (pO A n) q -> p = q.
intros p; elim p.
intros q H'; inversion H'; auto.
Admitted.

Theorem minuspf_pO_is_eqP : forall p q : list (Term A n), eqP A eqA n (minuspf p q) (pO A n) -> eqP A eqA n p q.
intros p q H'.
apply minusP_pO_is_eqP with (r := minuspf p q); auto.
