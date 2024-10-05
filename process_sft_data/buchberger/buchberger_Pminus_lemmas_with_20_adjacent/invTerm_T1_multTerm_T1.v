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

Theorem minuspf_pO_refl : forall p : list (Term A n), eqP A eqA n (minuspf p (pO A n)) p.
Admitted.

Theorem minuspf_pOmults : forall p : list (Term A n), eqP A eqA n (minuspf (pO A n) p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p).
Admitted.

Theorem mults_pO : forall (p : list (Term A n)) (a b : Term A n), eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> eqP A eqA n (pO A n) (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) b p)).
intros p; elim p.
simpl in |- *; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l H' a0 b H'0 H'1; simpl in |- *.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf (mults (A:=A) multA (n:=n) a0 l) (mults (A:=A) multA (n:=n) b l)); auto.
apply minuspf_inv3a; auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := multTerm (A:=A) multA (n:=n) (minusTerm (A:=A) minusA (n:=n) a0 b) a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem mults_minusTerm : forall (p : list (Term A n)) (a b : Term A n), eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> canonical A0 eqA ltM p -> eqP A eqA n (mults (A:=A) multA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) p) (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) b p)).
intros p; elim p.
simpl in |- *; auto.
intros a b H H0 H1; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l H' a0 b H'0 H'1 H'2; simpl in |- *; auto.
cut (canonical A0 eqA ltM l); try apply canonical_imp_canonical with (a := a); auto; intros Z0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX (minusTerm (A:=A) minusA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a) (multTerm (A:=A) multA (n:=n) b a)) (minuspf (mults (A:=A) multA (n:=n) a0 l) (mults (A:=A) multA (n:=n) b l))); auto.
apply (eqpP1 A eqA); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply multTerm_minusTerm_dist_l with (1 := cs); auto.
apply minuspf_inv3b; auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := multTerm (A:=A) multA (n:=n) (minusTerm (A:=A) minusA (n:=n) a0 b) a); auto.
apply nzeroP_multTerm with (1 := cs); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem order_pluspf : forall (l1 l2 : list (Term A n)) (a : Term A n), canonical A0 eqA ltM (pX a l1) -> canonical A0 eqA ltM (pX a l2) -> canonical A0 eqA ltM (pX a (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l1 l2)).
intros l1 l2 a H' H'0.
apply order_plusP with (1 := os) (plusA := plusA) (l1 := l1) (l2 := l2); auto.
apply pluspf_is_plusP; auto.
apply canonical_pluspf; auto.
apply canonical_imp_canonical with (a := a); auto.
Admitted.

Theorem order_minuspf : forall (l1 l2 : list (Term A n)) (a : Term A n), canonical A0 eqA ltM (pX a l1) -> canonical A0 eqA ltM (pX a l2) -> canonical A0 eqA ltM (pX a (minuspf l1 l2)).
intros l1 l2 a H' H'0.
apply eqp_imp_canonical with (1 := cs) (p := pX a (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (pX a l2))) in |- *; auto.
apply (eqT_sym A n); auto.
Admitted.

Theorem minusP_refl : forall p q r : list (Term A n), minusP p q r -> p = q -> r = pO A n.
intros p q r H'; elim H'; auto.
intros l1 H'0; rewrite <- H'0; simpl in |- *; auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3; generalize H'0.
rewrite (pX_invl A n a1 a2 l1 l2); auto; intros Ord.
absurd (ltT ltM a2 a2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3 H'4.
apply H'1; auto.
apply pX_invr with (a := a1) (b := a2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3 H'4; elim H'3; auto.
rewrite (pX_invl A n a1 a2 l1 l2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3; generalize H'0.
rewrite (pX_invl A n a1 a2 l1 l2); auto; intros Ord.
Admitted.

Theorem minuspf_refl_eq : forall p : list (Term A n), minuspf p p = pO A n.
Admitted.

Theorem minuspf_refl : forall p : list (Term A n), eqP A eqA n (minuspf p p) (pO A n).
intros p.
Admitted.

Theorem mults_comp_minuspf : forall (a : Term A n) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q)) (mults (A:=A) multA (n:=n) a (minuspf p q)).
intros a p q H' H'0 H'1.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a q))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a) q)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); auto.
Admitted.

Theorem minuspf_zero : forall (a : Term A n) (p q : list (Term A n)), eqP A eqA n (minuspf (pX a p) (pX a q)) (minuspf p q).
intros a p q; try assumption.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf p q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
Admitted.

Theorem pluspf_minuspf_id : forall p q : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (minuspf p q) q) p.
intros p q H' H'0.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)) q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) q)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); auto.
Admitted.

Theorem minusP_pO_refl_eq : forall p q : list (Term A n), minusP p (pO A n) q -> p = q.
Admitted.

Theorem minuspf_pO_refl_eq : forall p : list (Term A n), minuspf p (pO A n) = p.
intros p.
Admitted.

Theorem Opm_ind : forall (P : list (Term A n) -> list (Term A n) -> Prop) (p q : list (Term A n)), (forall p : list (Term A n), P (pO A n) p) -> (forall p : list (Term A n), P p (pO A n)) -> (forall (a b : Term A n) (p q : list (Term A n)), P (pX a p) q -> ltT ltM a b -> P (pX a p) (pX b q)) -> (forall (a b : Term A n) (p q : list (Term A n)), P p (pX b q) -> ltT ltM b a -> P (pX a p) (pX b q)) -> (forall (a b : Term A n) (p q : list (Term A n)), P p q -> eqT a b -> P (pX a p) (pX b q)) -> forall p q : list (Term A n), P p q.
intros P H' H'0 H'1 H'2 H'3 H'4 H'5 p; elim p; auto.
intros a l H'6 q; elim q; auto.
Admitted.

Theorem minuspf_eq_inv1 : forall (a : Term A n) (p q : list (Term A n)), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX a q) -> eqP A eqA n (pX a (minuspf p q)) (minuspf (pX a p) q).
intros a p q; case q; simpl in |- *; auto.
intros H' H'0; rewrite minuspf_pO_refl_eq; rewrite minuspf_pO_refl_eq; auto.
intros a0 l H' H'0.
change (eqP A eqA n (pX a (minuspf p (pX a0 l))) (minuspf (pX a p) (pX a0 l))) in |- *; apply minuspf_inv1; auto.
Admitted.

Theorem minuspf_pOmults_eq : forall p : list (Term A n), minuspf (pO A n) p = mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p.
Admitted.

Theorem minuspf_eq_inv2 : forall (a : Term A n) (p q : list (Term A n)), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX a q) -> eqP A eqA n (pX (invTerm (A:=A) invA (n:=n) a) (minuspf p q)) (minuspf p (pX a q)).
intros a p; elim p; auto.
intros q H' H'0; rewrite minuspf_pOmults_eq.
rewrite minuspf_pOmults_eq; simpl in |- *.
apply eqpP1; auto.
change (eqTerm (A:=A) eqA (n:=n) (invTerm (A:=A) invA (n:=n) a) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a)) in |- *.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) a)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a0 l H' q H'0 H'1.
change (eqP A eqA n (pX (invTerm (A:=A) invA (n:=n) a) (minuspf (pX a0 l) q)) (minuspf (pX a0 l) (pX a q))) in |- *.
rewrite <- (minuspf_inv2_eq a0 a l q); auto.
Admitted.

Definition inv : list (Term A n) -> Term A n -> Term A n.
intros p; case p.
intros a; exact (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a).
Admitted.

Theorem inv_prop : forall (a : Term A n) (p q : list (Term A n)), canonical A0 eqA ltM (pX a p) -> minuspf p (pX a q) = pX (inv p a) (minuspf p q).
intros a p q; case p; simpl in |- *; auto.
intros H'.
change (minuspf (pO A n) (pX a q) = pX (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a) (minuspf (pO A n) q)) in |- *.
rewrite (minuspf_pOmults_eq (pX a q)); simpl in |- *; auto.
rewrite (minuspf_pOmults_eq q); simpl in |- *; auto.
intros a0 l H'.
change (minuspf (pX a0 l) (pX a q) = pX (invTerm (A:=A) invA (n:=n) a) (minuspf (pX a0 l) q)) in |- *.
rewrite <- (minuspf_inv2_eq a0 a l q); auto.
Admitted.

Theorem pluspf_is_minuspf : forall p q : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> eqP A eqA n (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (minuspf p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
intros p q Opp Opq; apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (T1 A1 n) q); auto.
Admitted.

Definition sminus : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
Admitted.

Theorem invTerm_T1_multTerm_T1 : eqTerm (A:=A) eqA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) (T1 A1 n).
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)))); [ auto | idtac ].
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))); auto.
apply eqTerm_invTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply T1_multTerm_l with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply invTerm_invol with (1 := cs); auto.
