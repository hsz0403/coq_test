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

Theorem nf_divp : forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), ~ zerop A A0 eqA n ltM p -> ~ zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L) -> exists q : poly A0 eqA ltM, In q (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L :: L) /\ divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros p L; case p; unfold nf in |- *; auto.
unfold nf in |- *; auto.
intros x c; case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L (exist (fun l => canonical A0 eqA ltM l) x c)).
unfold LetP in |- *.
intros x0; case x0; auto.
intros x1 c0 H' H'0 H'1.
lapply (reducestar_divp (mks A A0 eqA n ltM x c) (mks A A0 eqA n ltM x1 c0) L); [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros r E; case E; intros H'2 H'3; case H'3; intros H'4 H'5; clear H'3 E H'6.
case H'2; [ intros H'3; clear H'2 | intros H'3; clear H'2 ].
exists (mks A A0 eqA n ltM (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c0)) x1) (canonical_mults _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ os (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c0)) x1 (unit_nZ _ _ _ _ _ _ _ _ _ cs n ltM (mks A A0 eqA n ltM x1 c0)) c0)); split; [ idtac | split ]; auto.
simpl in |- *; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := r); auto.
generalize H'5; rewrite <- H'3.
generalize c0; case x1; auto.
simpl in |- *; auto.
intros a l c1 H1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZa | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a l) c1)) a)); [ intros nZu | idtac ]; auto.
simpl in |- *; apply divTerm_def with (nZb := nZu); auto.
apply divTerm_on_eqT with (1 := cs) (a := a); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply multTerm_eqT; auto.
apply (eqT_sym A n); auto.
apply unit_T1; auto.
apply nzeroP_multTerm with (1 := cs); auto.
apply unit_nZ with (1 := cs); auto.
exists r; split; [ idtac | split ]; auto.
simpl in |- *; auto.
