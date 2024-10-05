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

Theorem Red_grobner : forall L : list (poly A0 eqA ltM), Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L -> Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec (Red L).
intros L H'.
apply def_grobner; auto.
intros p H'0.
lapply (grobner_def L); [ intros H'2; lapply (H'2 p); [ intros H'4 | idtac ] | idtac ]; auto.
case H'4; auto.
intros H'1; case H'1; intros q E; clear H'1.
right.
apply divp_reduce1 with (L1 := L) (q := q); auto.
intros r1 H'1 H'3.
lapply (Red_divp L r1); [ intros H'7; lapply H'7; [ intros H'8; clear H'7 | clear H'7 ] | idtac ]; auto.
case H'8; intros q0 E0; case E0; intros H'5 H'6; case H'6; intros H'7 H'9; clear H'6 E0 H'8.
exists q0; split; auto.
apply cb_Red_cb2; auto.
