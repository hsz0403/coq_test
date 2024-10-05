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

Theorem reduceplus_divp_lem : forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)), reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b -> canonical A0 eqA ltM a -> forall x y : poly A0 eqA ltM, s2p A A0 eqA n ltM x = a -> s2p A A0 eqA n ltM y = b -> ~ zerop A A0 eqA n ltM x -> exists r : poly A0 eqA ltM, In r (y :: Q) /\ divp A A0 eqA multA divA n ltM x r /\ ~ zerop A A0 eqA n ltM r.
intros a b Q H'; elim H'; auto.
intros x y H'0 H'1 x0 y0 H'2 H'3 H'4; exists y0; split; [ idtac | split ]; auto with datatypes.
generalize H'0 H'4; clear H'0 H'4; rewrite <- H'3; rewrite <- H'2; case x0; case y0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros H2 x2; case x2; auto.
intros t l H'5 H'6; inversion_clear H'6; auto.
intros t l H'0 x2; case x2; simpl in |- *; auto.
intros t0 l0 H'5 H'6; inversion_clear H'6; auto.
intros H5; apply divP_eqTerm_comp with (a := t) (1 := cs); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) t); [ intros Z | idtac ]; auto.
apply divTerm_def with (nZb := Z); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
generalize H'0 H'4; clear H'0 H'4; rewrite <- H'3; rewrite <- H'2; case x0; case y0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros H'0 x2; case x2; simpl in |- *; auto.
intros t l H'4 H'5; inversion_clear H'5.
intros x y z H'0 H'1 H'2 H'3 x0 y0 H'4 H'5 H'6.
cut (canonical A0 eqA ltM y); [ intros Z | idtac ].
2: apply canonical_reduce with (1 := cs) (3 := H'0); auto.
lapply (reduce_divp x0 (mks A A0 eqA n ltM y Z) Q); [ intros H'9 | idtac ]; auto.
2: rewrite H'4; simpl in |- *; auto.
case H'9; intros r E; case E; simpl in |- *; intros H'7 H'8; case H'8; intros H'10 H'11; clear H'8 E H'9.
case H'7; [ intros H'8; clear H'7 | intros H'8; clear H'7 ].
2: exists r; split; [ right | idtac ]; auto.
lapply H'2; [ intros H'7; lapply (H'7 (mks A A0 eqA n ltM y Z) y0); simpl in |- *; [ intros H'13; lapply H'13; [ intros H'14; lapply H'14; [ intros H'15; clear H'14 H'13 H'2 | clear H'14 H'13 H'2 ] | clear H'13 H'2 ] | clear H'2 ] | clear H'2 ]; auto.
case H'15; intros r0 E; case E; intros H'2 H'9; case H'9; intros H'12 H'13; clear H'9 E H'15.
exists r0; split; [ idtac | split ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := r); auto.
rewrite <- H'8; auto.
generalize H'11; rewrite <- H'8.
generalize Z; case y; auto.
