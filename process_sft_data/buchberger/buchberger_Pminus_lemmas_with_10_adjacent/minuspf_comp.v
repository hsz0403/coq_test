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

Theorem minusP_inv3a : forall (a b : Term A n) (p q s : list (Term A n)), eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> minusP (pX a p) (pX b q) s -> s = minuspf p q.
intros a b p q s Eqd Z0 H'; inversion_clear H'.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
apply uniq_minusp with (l := (p, q)); simpl in |- *; auto.
case H1; auto.
Admitted.

Theorem minusP_inv3b : forall (a b : Term A n) (p q s : list (Term A n)), eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> minusP (pX a p) (pX b q) s -> s = pX (minusTerm (A:=A) minusA (n:=n) a b) (minuspf p q).
intros a b p q s Eqd Z0 H'; inversion_clear H'.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
case Z0; auto.
apply pX_inj; auto.
apply uniq_minusp with (l := (p, q)); auto.
Admitted.

Theorem minuspf_inv1_eq : forall (a b : Term A n) (p q : list (Term A n)), ltT ltM b a -> pX a (minuspf p (pX b q)) = minuspf (pX a p) (pX b q).
intros a b p q H'; try assumption.
Admitted.

Theorem minuspf_inv2_eq : forall (a b : Term A n) (p q : list (Term A n)), ltT ltM a b -> pX (invTerm (A:=A) invA (n:=n) b) (minuspf (pX a p) q) = minuspf (pX a p) (pX b q).
intros a b p q H'; try assumption.
Admitted.

Theorem minuspf_inv3a_eq : forall (a b : Term A n) (p q : list (Term A n)), eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> minuspf p q = minuspf (pX a p) (pX b q).
intros a b p q H' Z; try assumption.
Admitted.

Theorem minuspf_inv3b_eq : forall (a b : Term A n) (p q : list (Term A n)), eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> pX (minusTerm (A:=A) minusA (n:=n) a b) (minuspf p q) = minuspf (pX a p) (pX b q).
intros a b p q H' Z; try assumption.
Admitted.

Theorem minuspf_inv1 : forall (a b : Term A n) (p q : list (Term A n)), ltT ltM b a -> eqP A eqA n (pX a (minuspf p (pX b q))) (minuspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
Admitted.

Theorem minuspf_inv2 : forall (a b : Term A n) (p q : list (Term A n)), ltT ltM a b -> eqP A eqA n (pX (invTerm (A:=A) invA (n:=n) b) (minuspf (pX a p) q)) (minuspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
Admitted.

Theorem minuspf_inv3a : forall (a b : Term A n) (p q : list (Term A n)), eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> eqP A eqA n (minuspf p q) (minuspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
Admitted.

Theorem minuspf_inv3b : forall (a b : Term A n) (p q : list (Term A n)), eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) -> eqP A eqA n (pX (minusTerm (A:=A) minusA (n:=n) a b) (minuspf p q)) (minuspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
Admitted.

Theorem mults_dist_minuspf : forall (p q : list (Term A n)) (a : Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n (mults (A:=A) multA (n:=n) a (minuspf p q)) (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q)).
intros p q a H' H'0 H'1.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) a (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a) q)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) a q))); auto.
Admitted.

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

Theorem minuspf_comp : forall p q r s : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> canonical A0 eqA ltM s -> eqP A eqA n p r -> eqP A eqA n q s -> eqP A eqA n (minuspf p q) (minuspf r s).
intros p q r s H' H'0 H'1 H'2 H'3 H'4; apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
apply minuspf_is_pluspf_mults; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec r (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) s)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
