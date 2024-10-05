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

Theorem nf_divp_zero : forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), ~ zerop A A0 eqA n ltM p -> zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L) -> exists q : poly A0 eqA ltM, In q L /\ divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros p L; case p; unfold nf in |- *; auto.
unfold nf in |- *; auto.
intros x c; case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L (exist (fun l : list (Term A n) => canonical A0 eqA ltM l) x c)).
unfold LetP in |- *.
simpl in |- *; intros x0; case x0; simpl in |- *; auto.
intros x1 c0 H' H'0 H'1.
lapply (reducestar_divp (mks A A0 eqA n ltM x c) (mks A A0 eqA n ltM x1 c0) L); simpl in |- *; [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros r E; case E; intros H'2 H'3; case H'3; intros H'4 H'5; clear H'3 E H'6.
case H'2; [ intros H'3; clear H'2 | intros H'3; clear H'2 ].
case H'5; rewrite <- H'3.
generalize c0 H'1; case x1; auto.
exists r; split; [ idtac | split ]; auto.
