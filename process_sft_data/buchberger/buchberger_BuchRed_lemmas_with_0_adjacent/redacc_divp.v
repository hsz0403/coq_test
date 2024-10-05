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

Theorem redacc_divp : forall (L1 L2 : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM), ~ zerop A A0 eqA n ltM p -> In p (L1 ++ L2) -> exists q : poly A0 eqA ltM, In q (redacc L1 L2 ++ L2) /\ divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros L1; elim L1; simpl in |- *; auto.
intros L2 p H' H'0; exists p; split; auto.
split; auto.
apply divp_id; auto.
unfold LetP in |- *.
intros a l H' L2 p H'0 H'1; case H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
case (zerop_dec A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2))); simpl in |- *; auto.
intros Z1.
lapply (nf_divp_zero a (l ++ L2)); [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7; clear H'4 E H'6.
lapply (H' L2 q); [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ]; auto.
case H'9; intros q0 E; case E; intros H'4 H'6; case H'6; intros H'8 H'10; clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := q); auto.
rewrite H'2; auto.
intros Z1.
lapply (nf_divp a (l ++ L2)); [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7; clear H'4 E H'6.
simpl in H'3.
case H'3; [ intros H'4; clear H'3 | intros H'4; clear H'3 ].
exists q; split; [ idtac | split ]; auto.
lapply (H' (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2) q); [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ]; auto.
case H'9; intros q0 E; case E; intros H'3 H'6; case H'6; intros H'8 H'10; clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
case (in_app_or _ _ _ H'3); auto.
simpl in |- *; auto with datatypes.
simpl in |- *; intros H'6; case H'6; [ intros H'9; clear H'6 | intros H'9; clear H'6 ]; auto.
auto with datatypes.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := q); auto.
case (in_app_or _ _ _ H'4); auto with datatypes.
rewrite H'2; auto.
case (zerop_dec A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2))); simpl in |- *; auto.
intros Z1.
case (in_app_or _ _ _ H'2); auto.
intros H'3.
lapply (H' (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a (l ++ L2) :: L2) p); [ intros H'6; lapply H'6; [ intros H'7; clear H'6 | clear H'6 ] | idtac ]; auto with datatypes.
case H'7; intros q E; case E; intros H'4 H'5; case H'5; intros H'6 H'8; clear H'5 E H'7.
exists q; split; auto.
case (in_app_or _ _ _ H'4); auto with datatypes.
simpl in |- *; auto.
intros H; case H; intros H1; auto with datatypes.
intros H; exists p; split; [ right | idtac ]; auto with datatypes.
split; auto.
apply divp_id; auto.
