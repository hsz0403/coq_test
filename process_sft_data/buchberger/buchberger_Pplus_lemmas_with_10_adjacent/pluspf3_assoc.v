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

Theorem pluspf_inv1_eq : forall a b p q, ltT ltM b a -> pX a (pluspf p (pX b q)) = pluspf (pX a p) (pX b q).
Admitted.

Theorem pluspf_inv2_eq : forall a b p q, ltT ltM a b -> pX b (pluspf (pX a p) q) = pluspf (pX a p) (pX b q).
Admitted.

Theorem pluspf_inv3a_eq : forall a b p q, eqT a b -> zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> pluspf p q = pluspf (pX a p) (pX b q).
Admitted.

Theorem pluspf_inv3b_eq : forall a b p q, eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q) = pluspf (pX a p) (pX b q).
Admitted.

Theorem order_pluspf : forall l1 l2 a, canonical A0 eqA ltM (pX a l1) -> canonical A0 eqA ltM (pX a l2) -> canonical A0 eqA ltM (pX a (pluspf l1 l2)).
intros l1 l2 a H' H'0.
apply order_plusP with (l1 := l1) (l2 := l2); auto.
apply canonical_pluspf; auto.
apply canonical_imp_canonical with (a := a); auto.
Admitted.

Theorem pluspf_inv1_eqa : forall a p q, canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX a q) -> pX a (pluspf p q) = pluspf (pX a p) q.
intros a p q; case q; auto.
rewrite <- pO_pluspf_inv2; auto.
rewrite <- pO_pluspf_inv2; auto.
intros a0 l H'0 H'1.
change (pX a (pluspf p (pX a0 l)) = pluspf (pX a p) (pX a0 l)) in |- *.
apply pluspf_inv1_eq; auto.
Admitted.

Theorem pluspf_inv2_eqa : forall a p q, canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX a q) -> pX a (pluspf p q) = pluspf p (pX a q).
intros a p; case p; auto.
intros q H'0 H'1.
rewrite <- pO_pluspf_inv1; auto.
rewrite <- pO_pluspf_inv1; auto.
intros a0 l q H'0 H'1.
change (pX a (pluspf (pX a0 l) q) = pluspf (pX a0 l) (pX a q)) in |- *.
apply pluspf_inv2_eq; auto.
Admitted.

Theorem p0_pluspf_l : forall p, eqP A eqA n (pluspf (pO A n) p) p.
Admitted.

Theorem p0_pluspf_r : forall p, eqP A eqA n (pluspf p (pO A n)) p.
Admitted.

Theorem plusTerm_is_pX : forall (a : Term A n) (p : list (Term A n)), canonical A0 eqA ltM (pX a p) -> eqP A eqA n (pluspf (pX a (pO A n)) p) (pX a p).
intros a p; case p; auto.
intros a0 l H'.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a (pluspf (pO A n) (a0 :: l))); auto.
change (eqP A eqA n (pluspf (pX a (pO A n)) (pX a0 l)) (pX a (pluspf (pO A n) (pX a0 l)))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply pluspf_inv1; auto.
Admitted.

Theorem pluspf_assoc : forall p q r, canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n (pluspf (pluspf p q) r) (pluspf p (pluspf q r)).
intros p q r H' H'0 H'1.
Admitted.

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
Admitted.

Theorem eqp_pluspf_com_r : forall p q r, eqP A eqA n p q -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> eqP A eqA n (pluspf r p) (pluspf r q).
intros p q r H'; generalize r; elim H'; clear r H'.
intros r H' H'0 H'1; rewrite <- pO_pluspf_inv2; auto.
intros ma mb p0 q0 H' H'0 H'1 r H'2 H'3 H'4.
cut (canonical A0 eqA ltM p0); [ intros C0 | apply canonical_imp_canonical with (a := ma) ]; auto.
cut (canonical A0 eqA ltM q0); [ intros C1 | apply canonical_imp_canonical with (a := mb) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) ma); [ intros nZ0 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := p0) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) mb); [ intros nZ1 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := q0) ]; auto.
generalize H'4; elim r; clear H'4 r.
intros H'4; rewrite <- pO_pluspf_inv1; rewrite <- pO_pluspf_inv1; auto.
intros a l H'4 H'5.
cut (canonical A0 eqA ltM l); [ intros C2 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ2 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := l) ]; auto.
change (eqP A eqA n (pluspf (pX a l) (pX ma p0)) (pluspf (pX a l) (pX mb q0))) in |- *.
case (ltT_dec A n ltM ltM_dec ma a); [ intros H0; case H0; clear H0 | idtac ]; intros H0.
cut (ltT ltM mb a); [ intros Or0 | idtac ].
rewrite <- (pluspf_inv1_eq a ma l p0); auto.
rewrite <- (pluspf_inv1_eq a mb l q0); auto.
apply eqT_compat_ltTl with (b := ma); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
cut (ltT ltM a mb); [ intros Or0 | idtac ]; auto.
rewrite <- (pluspf_inv2_eq a ma l p0); auto.
rewrite <- (pluspf_inv2_eq a mb l q0); auto.
apply eqT_compat_ltTr with (b := ma); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
cut (eqTerm eqA (plusTerm (A:=A) plusA (n:=n) a ma) (plusTerm (A:=A) plusA (n:=n) a mb)); [ intros eqTerm0 | idtac ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a ma)); intros Z0.
rewrite <- (pluspf_inv3a_eq a ma l p0); auto.
rewrite <- (pluspf_inv3a_eq a mb l q0); auto.
apply (eqT_trans A n) with (y := ma); auto; apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a ma); auto.
apply (eqT_sym A n); auto.
rewrite <- (pluspf_inv3b_eq a ma l p0); auto.
rewrite <- (pluspf_inv3b_eq a mb l q0); auto.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
red in |- *; intros H'6; apply Z0.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a mb); auto.
apply plusTerm_comp_r with (1 := cs); auto.
change (eqT a mb) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqT_sym A n); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply (eqT_sym A n); auto.
change (eqT a mb) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqT_sym A n); auto.
Admitted.

Theorem eqp_pluspf_com : forall p q r t, canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> canonical A0 eqA ltM r -> canonical A0 eqA ltM t -> eqP A eqA n p r -> eqP A eqA n q t -> eqP A eqA n (pluspf p q) (pluspf r t).
intros p q r t H' H'0 H'1 H'2 H'3 H'4.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf r q); auto.
apply eqp_pluspf_com_l; auto.
Admitted.

Definition splus : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (pluspf p1 p2); auto.
Admitted.

Theorem pluspf3_assoc : forall l, canonical A0 eqA ltM (fst l) -> canonical A0 eqA ltM (fst (snd l)) -> canonical A0 eqA ltM (snd (snd l)) -> eqP A eqA n (pluspf (pluspf (fst l) (fst (snd l))) (snd (snd l))) (pluspf (fst l) (pluspf (fst (snd l)) (snd (snd l)))).
intros l; pattern l in |- *.
apply (well_founded_ind (wf_lessP3 A n)).
intros x; case x; intros p z; case z; intros q r; simpl in |- *; clear x z; auto.
case p.
rewrite <- pO_pluspf_inv1; auto.
case q.
intros a l0; rewrite <- pO_pluspf_inv1; rewrite <- pO_pluspf_inv2; auto.
case r; simpl in |- *; auto.
intros a l0 a0 l1; rewrite <- pO_pluspf_inv2; rewrite <- pO_pluspf_inv2; auto.
intros a l0 a0 l1 a1 l2 H' H'0 H'1 H'2.
cut (canonical A0 eqA ltM (pX a l0)); [ clear H'2; intros H'2 | auto ].
cut (canonical A0 eqA ltM (pX a0 l1)); [ clear H'1; intros H'1 | auto ].
cut (canonical A0 eqA ltM (pX a1 l2)); [ clear H'0; intros H'0 | auto ].
cut (canonical A0 eqA ltM l0); [ intros C0 | apply canonical_imp_canonical with (a := a) ]; auto.
cut (canonical A0 eqA ltM l1); [ intros C1 | apply canonical_imp_canonical with (a := a0) ]; auto.
cut (canonical A0 eqA ltM l2); [ intros C2 | apply canonical_imp_canonical with (a := a1) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZ0 | apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l0) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros nZ1 | apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l1) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1); [ intros nZ2 | apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l2) ]; auto.
change (eqP A eqA n (pluspf (pluspf (pX a1 l2) (pX a0 l1)) (pX a l0)) (pluspf (pX a1 l2) (pluspf (pX a0 l1) (pX a l0)))) in |- *.
case (ltT_dec A n ltM ltM_dec a1 a0); [ intros H0; case H0; clear H0 | idtac ]; intros H0.
case (ltT_dec A n ltM ltM_dec a0 a); [ intros H1; case H1; clear H1 | idtac ]; intros H1.
cut (ltT ltM a1 a); [ intros Ord0 | apply (ltT_trans A _ _ os) with (y := a0) ]; auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv2_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply eqpP1; auto.
rewrite (pluspf_inv2_eq a1 a0 l2 l1); auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
rewrite <- (pluspf_inv1_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
apply eqpP1; auto.
apply H' with (y := (pX a1 l2, (l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
cut (ltT ltM a1 a); [ intros Ord0 | apply eqT_compat_ltTr with (b := a0) ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a)); intros Z0.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv3a_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
apply H' with (y := (pX a1 l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l2)); auto.
repeat rewrite (plus_comm (size A n l1)); auto.
cut (ltT ltM a1 (plusTerm (A:=A) plusA (n:=n) a0 a)); [ intros Ord1 | apply eqT_compat_ltTr with (b := a0); auto; apply (eqT_sym A n); apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv3b_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
rewrite <- (pluspf_inv2_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0)) ; auto.
apply eqpP1; auto.
apply H' with (y := (pX a1 l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l2)); auto.
repeat rewrite (plus_comm (size A n l1)); auto.
rewrite <- (pluspf_inv1_eq a1 a0 l2 l1); auto.
case (ltT_dec A n ltM ltM_dec a0 a); [ intros H1; case H1; clear H1 | idtac ]; intros H1.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
case (ltT_dec A n ltM ltM_dec a1 a); [ intros H2; case H2; clear H2 | idtac ]; intros H2.
rewrite <- (pluspf_inv2_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply eqpP1; auto.
rewrite (pluspf_inv1_eq a1 a0 l2 l1); auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
rewrite <- (pluspf_inv1_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
apply eqpP1; auto.
rewrite (pluspf_inv2_eq a0 a l1 l0); auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
cut (ltT ltM a0 (plusTerm (A:=A) plusA (n:=n) a1 a)); [ intros Ord1 | apply eqT_compat_ltTr with (b := a1); auto; apply (eqT_sym A n); apply (plusTerm_eqT1 A plusA n) ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a1 a)); intros Z0.
rewrite <- (pluspf_inv3a_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv3a_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply H' with (y := (l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
rewrite <- (pluspf_inv3b_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv3b_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply eqpP1; auto.
apply H' with (y := (l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
cut (ltT ltM a a1); [ intros Ord0 | apply (ltT_trans A n ltM os) with (y := a0) ]; auto with arith.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
apply eqpP1; auto.
rewrite (pluspf_inv1_eq a0 a l1 l0); auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
cut (ltT ltM a a1); [ intros Ord0 | apply eqT_compat_ltTl with (b := a0); auto ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a)); intros Z0.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eqa a1 l2 (pluspf l1 l0)); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
apply eqpP1; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf l2 (pluspf (pX a0 l1) (pX a l0))); auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
apply order_pluspf; auto.
apply canonical_skip_fst with (b := a0); auto.
apply canonical_skip_fst with (b := a); auto.
cut (ltT ltM (plusTerm (A:=A) plusA (n:=n) a0 a) a1); [ intros Ord1 | apply eqT_compat_ltTl with (b := a0); auto; apply (eqT_sym A n); auto; apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv1_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0)) ; auto.
apply eqpP1; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf l2 (pluspf (pX a0 l1) (pX a l0))); auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a1 a0)); intros Z0.
rewrite <- (pluspf_inv3a_eq a1 a0 l2 l1); auto.
case (ltT_dec A n ltM ltM_dec a1 a); [ intros H2; case H2; clear H2 | idtac ]; intros H2.
cut (ltT ltM a0 a); [ intros Ord0 | apply eqT_compat_ltTl with (b := a1) ]; auto.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a (pluspf (pluspf (pX a1 l2) (pX a0 l1)) l0)); auto.
rewrite <- (pluspf_inv3a_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv2_eqa a (pluspf l2 l1) l0); auto.
apply order_pluspf; auto.
apply canonical_skip_fst with (b := a1); auto.
apply canonical_skip_fst with (b := a0); auto.
apply eqpP1; auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
cut (ltT ltM a a0); [ intros Ord0 | apply eqT_compat_ltTr with (b := a1) ]; auto.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv3a_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
apply H' with (y := (l2, (l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a)); intros Z1.
cut (eqT a0 a); [ intros eqTerm0 | apply (eqT_trans A n) with (y := a1); auto; apply (eqT_sym A n) ]; auto.
cut (eqT a (plusTerm (A:=A) plusA (n:=n) a1 a0)); [ intros eqTerm1 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n); auto; apply (plusTerm_eqT2 A plusA n) ]; auto.
cut (eqT (plusTerm (A:=A) plusA (n:=n) a a1) a0); [ intros eqTerm2 | apply (eqT_trans A n) with (y := a); [ apply (plusTerm_eqT1 A plusA n) | apply (eqT_trans A n) with (y := a1) ]; auto; apply (eqT_sym A n) ]; auto.
cut (eqT (plusTerm (A:=A) plusA (n:=n) a1 a) a0); [ intros eqTerm3 | apply (eqT_trans A n) with (y := a); auto; [ apply (plusTerm_eqT2 A plusA n) | apply (eqT_sym A n) ] ]; auto.
cut (eqT a1 (plusTerm (A:=A) plusA (n:=n) a a0)); [ intros eqTerm4 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n); apply (plusTerm_eqT2 A plusA n); auto; apply (eqT_sym A n) ]; auto.
cut (eqT a1 (plusTerm (A:=A) plusA (n:=n) a0 a)); [ intros eqTerm5 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n); apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eqa a (pluspf l2 l1) l0); auto.
rewrite <- (pluspf_inv1_eqa a1 l2 (pluspf l1 l0)); auto.
apply eqpP1; auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a (plusTerm (A:=A) plusA (n:=n) a1 a0)); auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a a0)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a a1) a0); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a) a0); auto.
apply plusTerm_comp_l with (1 := cs); auto.
apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply zeroP_plusTermr with (1 := cs); auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a0); auto.
apply (eqT_sym A n); auto.
apply canonical_pX_eqT with (a := a); auto.
apply (eqT_sym A n); auto.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a1); auto.
apply canonical_pX_eqT with (a := a0); auto.
cut (eqT a0 a); [ intros Ord0 | apply (eqT_trans A n) with (y := a1); auto; apply (eqT_sym A n) ]; auto.
cut (eqT a (plusTerm (A:=A) plusA (n:=n) a1 a0)); [ intros eqTerm1 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n); auto; apply (plusTerm_eqT2 A plusA n) ]; auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv3b_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0)) ; auto.
rewrite <- (pluspf_inv2_eqa a (pluspf l2 l1) l0); auto.
apply eqpP1; auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a (plusTerm (A:=A) plusA (n:=n) a1 a0)); auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a); auto.
apply plusTerm_com with (1 := cs); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a1); auto.
apply canonical_pX_eqT with (a := a0); auto.
apply (eqT_trans A n) with (y := a); auto; apply (eqT_sym A n); auto.
apply (plusTerm_eqT2 A plusA n); auto.
red in |- *; intros H'3; absurd (zeroP (A:=A) A0 eqA (n:=n) a); auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply zeroP_plusTerml with (1 := cs); auto.
apply (eqT_sym A n); auto.
rewrite <- (pluspf_inv3b_eq a1 a0 l2 l1); auto.
case (ltT_dec A n ltM ltM_dec a0 a); [ intros H1; case H1; clear H1 | idtac ]; intros H1.
cut (ltT ltM a1 a); [ intros Ord0 | apply eqT_compat_ltTl with (b := a0); auto; apply (eqT_sym A n) ]; auto.
cut (ltT ltM (plusTerm (A:=A) plusA (n:=n) a1 a0) a); [ intros Ord1 | apply eqT_compat_ltTl with (b := a1); auto; apply (eqT_sym A n); apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
rewrite <- (pluspf_inv2_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0) ; auto.
apply eqpP1; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (pluspf (pX a1 l2) (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv3b_eq a1 a0 l2 l1); auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
cut (ltT ltM a a1); [ intros Ord0 | apply eqT_compat_ltTr with (b := a0); auto; apply (eqT_sym A n) ]; auto.
cut (ltT ltM a (plusTerm (A:=A) plusA (n:=n) a1 a0)); [ intros Ord1 | apply eqT_compat_ltTr with (b := a0); auto; apply (eqT_sym A n); apply (plusTerm_eqT2 A plusA n) ]; auto.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv3b_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
rewrite <- (pluspf_inv1_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0) ; auto.
apply eqpP1; auto.
apply H' with (y := (l2, (l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
cut (eqT a1 (plusTerm (A:=A) plusA (n:=n) a0 a)); [ intros eqTerm1 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n); apply (plusTerm_eqT1 A plusA n) ]; auto.
cut (eqT a1 a); [ intros eqT0 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n) ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a)); intros Z1.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eqa a1 l2 (pluspf l1 l0)); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a)); [ intros Z2 | idtac ].
rewrite <- (pluspf_inv3b_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0) ; auto.
apply eqpP1; auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a)); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply zeroP_plusTermr with (1 := cs); auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply (eqT_trans A n) with (y := a1); auto.
apply (plusTerm_eqT1 A plusA n); auto.
red in |- *; intros H'3; absurd (zeroP (A:=A) A0 eqA (n:=n) a1); auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a)); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply zeroP_plusTermr with (1 := cs); auto.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a0); auto.
apply (eqT_trans A n) with a; auto.
apply (eqT_sym A n); auto.
apply canonical_pX_eqT with (a := a); auto.
apply (eqT_sym A n); auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
cut (eqTerm eqA (plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a) (plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a))); [ intros eqTerm0 | idtac ].
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a)); intros Z2.
rewrite <- (pluspf_inv3a_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0) ; auto.
rewrite <- (pluspf_inv3a_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0)) ; auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a); auto.
apply (eqT_trans A n) with (y := a0); auto.
apply (plusTerm_eqT2 A plusA n); auto.
rewrite <- (pluspf_inv3b_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0) ; auto.
rewrite <- (pluspf_inv3b_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0)) ; auto.
apply eqpP1; auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply nzeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a); auto.
apply (eqT_trans A n) with (y := a0); auto.
apply (plusTerm_eqT2 A plusA n); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
