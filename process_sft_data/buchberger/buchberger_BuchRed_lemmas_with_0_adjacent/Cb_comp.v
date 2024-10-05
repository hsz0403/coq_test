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

Theorem Cb_comp : forall L1 L2 : list (poly A0 eqA ltM), (forall p : poly A0 eqA ltM, In p L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L2) -> forall q : poly A0 eqA ltM, Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L2.
intros L1 L2 H' q; case q; simpl in |- *.
intros x H'0 H'1.
apply CombLinear_compo with (1 := cs) (L1 := L1); auto.
intros q0 H'2.
case inPolySet_inv1 with (1 := H'2); auto.
intros q1 H; elim H; intros H0 H1; clear H.
lapply (H' q1); [ intros H'6 | idtac ]; auto.
generalize H'6 H1; case q1; simpl in |- *; auto.
intros x0 H'5 H'7 H'8; rewrite H'8; auto.
