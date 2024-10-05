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

Theorem zerop_elim_cb : forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM), zerop A A0 eqA n ltM p -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L.
intros L p q H' H'0.
apply Cb_comp with (L1 := p :: L); auto.
simpl in |- *; auto.
intros p0 H'1; case H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
generalize H'; case p; simpl in |- *; auto.
intros x; case x; simpl in |- *; auto.
intros H'1 H'3; try assumption.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec L (pO A n)) in |- *.
apply CombLinear_0; auto.
intros a l H'1 H'3; elim H'3; auto.
apply Cb_id with (1 := cs); auto.
