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

Theorem minusP_inv1 : forall (a b : Term A n) (p q s : list (Term A n)), minusP (pX a p) (pX b q) s -> ltT ltM b a -> s = pX a (minuspf p (pX b q)).
intros a b p q s H'; inversion_clear H'; intros.
apply pX_inj; auto.
apply uniq_minusp with (l := (p, pX b q)); simpl in |- *; auto.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
Admitted.

Theorem minusP_inv2 : forall (a b : Term A n) (p q s : list (Term A n)), minusP (pX a p) (pX b q) s -> ltT ltM a b -> s = pX (invTerm (A:=A) invA (n:=n) b) (minuspf (pX a p) q).
intros a b p q s H'; inversion_clear H'; intros.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
apply pX_inj; auto.
Admitted.

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

Theorem minuspf_comp : forall p q r s : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> canonical A0 eqA ltM s -> eqP A eqA n p r -> eqP A eqA n q s -> eqP A eqA n (minuspf p q) (minuspf r s).
intros p q r s H' H'0 H'1 H'2 H'3 H'4; apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
apply minuspf_is_pluspf_mults; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec r (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) s)); auto.
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

Theorem minuspf_inv1_eq : forall (a b : Term A n) (p q : list (Term A n)), ltT ltM b a -> pX a (minuspf p (pX b q)) = minuspf (pX a p) (pX b q).
intros a b p q H'; try assumption.
rewrite (minusP_inv1 a b p q (minuspf (pX a p) (pX b q))); auto.
