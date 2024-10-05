Require Export Pcomb.
Require Export Pcrit.
Require Export Buch.
Require Export Fred.
Require Import Buch.
Section BuchRed.
Load hCoefStructure.
Load hOrderStructure.
Load hBuch.
Definition reducep (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM) : Prop := reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec L (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM q).
Hint Resolve zerop_nf_cb : core.
Definition redacc : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros H'; elim H'.
intros L; exact (nil (A:=poly A0 eqA ltM)).
intros a p Rec Acc.
apply LetP with (A := poly A0 eqA ltM) (h := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (p ++ Acc)).
intros u H'0; case (zerop_dec A A0 eqA n ltM u); intros Z.
exact (Rec Acc).
exact (u :: Rec (u :: Acc)).
Defined.
Definition Red (L : list (poly A0 eqA ltM)) : list (poly A0 eqA ltM) := redacc L nil.
Definition redbuch (L : list (poly A0 eqA ltM)) : list (poly A0 eqA ltM) := Red (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L).
End BuchRed.

Theorem divp_reduce1 : forall (p : poly A0 eqA ltM) (L1 L2 : list (poly A0 eqA ltM)), (forall r1 : poly A0 eqA ltM, In r1 L1 -> ~ zerop A A0 eqA n ltM r1 -> exists r2 : poly A0 eqA ltM, In r2 L2 /\ divp A A0 eqA multA divA n ltM r1 r2) -> forall q : poly A0 eqA ltM, reducep L1 p q -> exists r : poly A0 eqA ltM, reducep L2 p r.
intros p L1 L2 H' q; case p; case q; simpl in |- *; auto.
intros x H'0 x0 c H'1; generalize c; unfold reducep in H'1; simpl in H'1; elim H'1; auto.
intros a b nZb p0 q0 r H'2 H'3 H'4 c0.
case inPolySet_inv1 with (1 := H'2).
intros q1 E; case E; intros H4 H5; clear E.
elim (H' q1); [ intros r2 E; elim E; intros H'10 H'11; clear E | idtac | idtac ]; auto.
generalize H'10 H'11 H5 c0 H4; case q1; simpl in |- *; auto.
intros x1 c1; case r2; simpl in |- *; auto.
intros x2; case x2; simpl in |- *; auto.
generalize c1; case x1; auto.
intros c2 c3 H'6 H'8 H'9 c4 H'12; discriminate.
intros t l c2 c3 H'6 H'8; elim H'8.
intros a0 l c2; generalize c1; case x1; auto.
intros c3 H'6 H'8; elim H'8.
intros t l0 c3 H'6 H'8 H'9 c4 H'12.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros nZa0 | idtac ].
cut (canonical A0 eqA ltM (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a0 nZa0 p0 l)); [ intros Z | idtac ].
exists (mks A A0 eqA n ltM (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a0 nZa0 p0 l) Z); simpl in |- *; auto.
red in |- *; simpl in |- *; apply reducetop_sp with (1 := cs); auto.
change (inPolySet A A0 eqA n ltM (s2p A A0 eqA n ltM (mks A A0 eqA n ltM (pX a0 l) c2)) L2) in |- *.
apply in_inPolySet; auto.
simpl in |- *.
red in |- *; intros H'13; inversion H'13.
injection H'9; intros.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
rewrite H0; auto.
apply canonical_spminusf_full with (1 := cs); auto.
injection H'9; intros.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
rewrite H0; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
generalize H5; case q1; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros c1 H'6; discriminate.
intros a b p0 q0 H'2 H'3 H'4 c0.
cut (canonical A0 eqA ltM p0); [ intro | apply canonical_imp_canonical with (a := a); auto ].
case (H'3 H); intros r; case r.
intros x1 H'6 H'7.
cut (canonical A0 eqA ltM (pX b x1)); [ intros Z | idtac ].
exists (mks A A0 eqA n ltM (pX b x1) Z); simpl in |- *; auto.
red in |- *; simpl in |- *; red in H'7; simpl in H'7; auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a x1); auto.
apply ltP_pX_canonical; auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
apply ltP_trans with (y := p0); auto.
apply ltP_reduce with (1 := cs) (3 := H'7); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
