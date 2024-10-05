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

Theorem Cb_nf : forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p L :: L).
intros p L; unfold nf in |- *.
case (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os L p); auto.
case p.
unfold LetP in |- *; intros x H' x0; case x0; simpl in |- *.
intros x1 c H'0.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec (mks A A0 eqA n ltM (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c)) x1) (canonical_mults A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM os (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c)) x1 (unit_nZ A A0 A1 eqA plusA invA minusA multA divA cs n ltM (mks A A0 eqA n ltM x1 c)) c) :: L) x) in |- *.
apply CombLinear_compo with (1 := cs) (L1 := mks A A0 eqA n ltM x1 c :: L); auto.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec (mks A A0 eqA n ltM x1 c :: L) (s2p A A0 eqA n ltM (mks A A0 eqA n ltM x H'))) in |- *.
apply reducestar_cb2 with (1 := cs); auto.
intros q H'1; inversion H'1; auto.
2: apply CombLinear_id with (1 := cs); auto.
2: apply inskip; auto.
generalize c H2; case x1; auto.
intros c0 H'2; inversion H'2.
intros a0 l c0 H'2.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0))); [ intros nZu | idtac ]; auto.
apply CombLinear_1 with (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) nZu) (p := pO A n) (q := mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) (pX a0 l)); auto.
simpl in |- *; auto.
change (inPolySet A A0 eqA n ltM (pX (multTerm (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) a0) (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) l)) (exist (fun a1 => canonical A0 eqA ltM a1) (pX (multTerm (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) a0) (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) l)) (canonical_mults A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM os (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) (pX a0 l) (unit_nZ _ _ _ _ _ _ _ _ _ cs _ ltM (mks A A0 eqA n ltM (pX a0 l) c0)) c0) :: L)) in |- *.
apply incons; auto.
apply CombLinear_0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) nZu) (mults (A:=A) multA (n:=n) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) (a0 :: l))); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)) nZu) (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0))) (a0 :: l)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (T1 A1 n) (a0 :: l)); auto.
rewrite H'2; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply unit_T1; auto.
apply unit_nZ with (1 := cs); auto.
