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

Lemma plusP_inv : forall p q l (a b : Term A n), plusP (pX a p) (pX b q) l -> exists l1 : _, ltT ltM b a /\ plusP p (pX b q) l1 /\ l = pX a l1 \/ ltT ltM a b /\ plusP (pX a p) q l1 /\ l = pX b l1 \/ eqT a b /\ (zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) /\ plusP p q l \/ ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) /\ plusP p q l1 /\ l = pX (plusTerm (A:=A) plusA (n:=n) a b) l1).
intros p q l a b H'; simple inversion H'.
discriminate H.
discriminate H0.
rewrite <- H3; rewrite (pX_invl _ _ a2 b l2 q H2); rewrite (pX_invr _ _ l2 q a2 b H2); rewrite (pX_invl _ _ a1 a l1 p H1); rewrite (pX_invr _ _ l1 p a1 a H1).
intros H'0 H'1; exists l3; left; split; [ idtac | split; [ try assumption | idtac ] ]; auto.
rewrite <- H3.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- (pX_invl _ _ a2 b l2 q H3); rewrite <- (pX_invl _ _ a1 a l1 p H2); auto.
rewrite <- (pX_invr _ _ l2 q a2 b H3); rewrite <- (pX_invr _ _ l1 p a1 a H2); auto.
rewrite <- H4; auto.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- (pX_invl _ _ a2 b l2 q H3); rewrite <- (pX_invl _ _ a1 a l1 p H2); auto.
rewrite <- (pX_invr _ _ l2 q a2 b H3); rewrite <- (pX_invr _ _ l1 p a1 a H2); auto.
intros H'0 H'1; exists l3; right; left; split; [ idtac | split; [ try assumption | idtac ] ]; auto.
rewrite <- (pX_invl _ _ a2 b l2 q H2); rewrite <- (pX_invl _ _ a1 a l1 p H1); auto.
rewrite <- (pX_invl _ _ a1 a l1 p H1); rewrite <- (pX_invr _ _ l2 q a2 b H2); rewrite <- (pX_invr _ _ l1 p a1 a H1); auto.
rewrite <- H3; rewrite <- (pX_invl _ _ a2 b l2 q H2); auto.
