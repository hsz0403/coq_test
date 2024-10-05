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

Theorem canonical_plusP : forall l1 l2 l3, plusP l1 l2 l3 -> canonical A0 eqA ltM l1 -> canonical A0 eqA ltM l2 -> canonical A0 eqA ltM l3.
intros l1 l2 l3 H'; elim H'; auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4; try assumption.
apply order_plusP with (l1 := l4) (l2 := pX a2 l5); auto.
apply canonical_cons; auto.
apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l4); auto.
apply H'2; auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a1); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply H'1; auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a1); auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply order_plusP with (l1 := l4) (l2 := l5); auto.
apply canonical_pX_eqT with (a := a1); auto.
apply (eqT_sym A n (plusTerm (A:=A) plusA (n:=n) a1 a2)).
apply plusTerm_eqT1; auto.
apply canonical_pX_eqT with (a := a2); auto; auto.
apply (eqT_sym A n (plusTerm (A:=A) plusA (n:=n) a1 a2)).
apply plusTerm_eqT2; auto.
apply H'1.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a1); auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4.
apply order_plusP with (l1 := pX a1 l4) (l2 := l5); auto.
apply canonical_cons; auto.
apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l5); auto.
apply H'2; auto.
Admitted.

Theorem canonical_pluspf : forall l1 l2, canonical A0 eqA ltM l1 -> canonical A0 eqA ltM l2 -> canonical A0 eqA ltM (pluspf l1 l2).
intros l1 l2 H' H'0; generalize (pluspf_is_plusP l1 l2); intros u1.
Admitted.

Theorem pO_plusP_inv1 : forall p q, plusP (pO A n) p q -> p = q.
intros p; elim p.
intros q H'; inversion H'; auto.
Admitted.

Theorem pO_plusP_inv2 : forall p q, plusP p (pO A n) q -> p = q.
intros p; elim p.
intros q H'; inversion H'; auto.
Admitted.

Theorem plusP_decomp : forall a p, canonical A0 eqA ltM (pX a p) -> plusP (pX a (pO A n)) p (pX a p).
intros a p; case p; auto.
intros m l H'; try assumption.
change (plusP (pX a (pO A n)) (pX m l) (pX a (pX m l))) in |- *.
apply mainu1; auto.
Admitted.

Theorem plusP_inv1 : forall a b p q s, plusP (pX a p) (pX b q) s -> ltT ltM b a -> s = pX a (pluspf p (pX b q)).
unfold pX in |- *; intros a b p q s H'; inversion_clear H'; intros.
change (pX a l3 = pX a (pluspf p (pX b q))) in |- *; apply pX_inj; auto.
apply uniq_plusp with (l := (p, pX b q)); simpl in |- *; auto.
absurd (eqT b a); auto.
apply eqT_sym; auto.
absurd (eqT b a); auto.
apply eqT_sym; auto.
Admitted.

Theorem plusP_inv2 : forall a b p q s, plusP (pX a p) (pX b q) s -> ltT ltM a b -> s = pX b (pluspf (pX a p) q).
intros a b p q s H'; inversion_clear H'; intros.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
apply pX_inj; auto.
Admitted.

Theorem plusP_inv3a : forall a b p q s, eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> plusP (pX a p) (pX b q) s -> s = pluspf p q.
intros a b p q s Eqd Z0 H'; inversion_clear H'; intros.
absurd (eqT b a); auto.
apply eqT_sym; auto.
apply uniq_plusp with (l := (p, q)); auto.
elim H1; auto.
Admitted.

Theorem plusP_inv3b : forall a b p q s, eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> plusP (pX a p) (pX b q) s -> s = pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q).
unfold pX in |- *; intros a b p q s Eqd Z0 H'; inversion_clear H'; intros.
absurd (eqT b a); auto.
apply eqT_sym; auto.
elim Z0; try assumption.
change (pX (plusTerm (A:=A) plusA (n:=n) a b) l3 = pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q)) in |- *.
apply pX_inj; auto.
apply uniq_plusp with (l := (p, q)); auto.
Admitted.

Theorem pluspf_inv1 : forall a b p q, ltT ltM b a -> eqP A eqA n (pX a (pluspf p (pX b q))) (pluspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
Admitted.

Theorem pluspf_inv3a : forall a b p q, eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> eqP A eqA n (pluspf p q) (pluspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
Admitted.

Theorem pluspf_inv3b : forall a b p q, eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> eqP A eqA n (pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q)) (pluspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
Admitted.

Theorem plusP_com : forall p q r s, plusP p q r -> plusP q p s -> eqP A eqA n r s.
intros p q r s H'; generalize s; elim H'; clear s H'; auto.
intros l1 s H'; try assumption.
rewrite (pO_plusP_inv2 l1 s); auto.
intros l1 s H'; rewrite (pO_plusP_inv1 l1 s); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 s H'2.
rewrite (plusP_inv2 a2 a1 l2 l1 s); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 H'2 s R.
rewrite (plusP_inv3a a2 a1 l2 l1 s); auto.
apply (eqT_sym A n a1); auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a1 a2); auto.
apply plusTerm_com with (1 := cs); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 H'2 s H'3.
rewrite (plusP_inv3b a2 a1 l2 l1 s); auto.
apply eqpP1; auto; apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n a1); auto.
red in |- *; intros H'4; apply H'2.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a2 a1); auto.
apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 s H'2.
Admitted.

Theorem pluspf_com : forall p q, eqP A eqA n (pluspf p q) (pluspf q p).
Admitted.

Theorem plusP_zero_pOl : forall p q, plusP (pO A n) p q -> eqP A eqA n p q.
Admitted.

Theorem plusP_zero_pOr : forall p q, plusP p (pO A n) q -> eqP A eqA n p q.
Admitted.

Theorem plusP_uniq_eqP : forall p q r s, plusP p q r -> plusP p q s -> eqP A eqA n r s.
Admitted.

Theorem pO_pluspf_inv1 : forall p, p = pluspf (pO A n) p.
intros p.
Admitted.

Theorem pO_pluspf_inv2 : forall p, p = pluspf p (pO A n).
intros p.
Admitted.

Theorem pluspf_inv1_eq : forall a b p q, ltT ltM b a -> pX a (pluspf p (pX b q)) = pluspf (pX a p) (pX b q).
Admitted.

Theorem pluspf_inv2 : forall a b p q, ltT ltM a b -> eqP A eqA n (pX b (pluspf (pX a p) q)) (pluspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
rewrite (plusP_inv2 a b p q (pluspf (pX a p) (pX b q))); auto.
