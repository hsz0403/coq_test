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

Theorem grobner_def : forall L : list (poly A0 eqA ltM), Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L -> forall p : poly A0 eqA ltM, Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L -> zerop A A0 eqA n ltM p \/ (exists q : poly A0 eqA ltM, reducep L p q).
intros L H'; inversion H'; auto.
intros p H'0.
case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L p).
intros x H'1; inversion H'.
lapply (H0 (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM x)); [ intros H'4; lapply H'4; [ clear H'4 | clear H'4 ] | idtac ]; auto.
inversion H'1; auto.
inversion H1; auto.
intros H'2; left.
cut (eqP A eqA n (s2p A A0 eqA n ltM p) (pO A n)); auto.
case p; simpl in |- *; auto.
intros x1; case x1; auto.
intros a l H'3 H'4; inversion H'4.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := s2p A A0 eqA n ltM x); auto.
intros H'2; right; cut (canonical A0 eqA ltM y); auto.
intros H'3; exists (mks A A0 eqA n ltM y H'3); generalize H5; case p; simpl in |- *; auto.
apply canonical_reduce with (1 := cs) (3 := H5); auto.
generalize H'0; case p; simpl in |- *; auto.
generalize H'0; case p; simpl in |- *; auto.
