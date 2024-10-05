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

Theorem eqp_pluspf_com_l : forall p q r, eqP A eqA n p q -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n (pluspf p r) (pluspf q r).
intros p q r H'; generalize r; elim H'; clear r H'.
intros r H' H'0 H'1; rewrite <- pO_pluspf_inv1; auto.
intros ma mb p0 q0 H' H'0 H'1 r H'2 H'3 H'4.
cut (canonical A0 eqA ltM p0); [ intros C0 | apply canonical_imp_canonical with (a := ma) ]; auto.
cut (canonical A0 eqA ltM q0); [ intros C1 | apply canonical_imp_canonical with (a := mb) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) ma); [ intros nZ0 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := p0) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) mb); [ intros nZ1 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := q0) ]; auto.
generalize H'4; elim r; clear H'4 r.
intros H'4; rewrite <- pO_pluspf_inv2; rewrite <- pO_pluspf_inv2; auto.
intros a l H'4 H'5.
cut (canonical A0 eqA ltM l); [ intros C2 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ2 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := l) ]; auto.
change (eqP A eqA n (pluspf (pX ma p0) (pX a l)) (pluspf (pX mb q0) (pX a l))) in |- *.
case (ltT_dec A n ltM ltM_dec ma a); [ intros H0; case H0; clear H0 | idtac ]; intros H0.
cut (ltT ltM mb a); [ intros Or0 | idtac ].
rewrite <- (pluspf_inv2_eq ma a p0 l); auto.
rewrite <- (pluspf_inv2_eq mb a q0 l); auto.
apply eqT_compat_ltTl with (b := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
cut (ltT ltM a mb); [ intros Or0 | idtac ]; auto.
rewrite <- (pluspf_inv1_eq ma a p0 l); auto.
rewrite <- (pluspf_inv1_eq mb a q0 l); auto.
apply eqT_compat_ltTr with (b := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
cut (eqTerm eqA (plusTerm (A:=A) plusA (n:=n) ma a) (plusTerm (A:=A) plusA (n:=n) mb a)); [ intros eqTerm0 | idtac ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) ma a)); intros Z0.
rewrite <- (pluspf_inv3a_eq ma a p0 l); auto.
rewrite <- (pluspf_inv3a_eq mb a q0 l); auto.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) ma a); auto.
rewrite <- (pluspf_inv3b_eq ma a p0 l); auto.
rewrite <- (pluspf_inv3b_eq mb a q0 l); auto.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
red in |- *; intros H'6; apply Z0.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) mb a); auto.
apply plusTerm_comp_l with (1 := cs); auto.
change (eqT mb a) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply plusTerm_comp_l with (1 := cs); auto.
change (eqT mb a) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
