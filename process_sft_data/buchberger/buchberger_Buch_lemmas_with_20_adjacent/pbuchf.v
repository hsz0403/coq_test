Require Export List.
Require Import Inclusion.
Require Import Inverse_Image.
Require Import Wf_nat.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Relation_Operators_compat.
Require Import Lexicographic_Product.
Require Import LetP.
Require Export WfR0.
Require Import Arith.
Require Import Relation_Operators.
Require Import Lexicographic_Product.
Section Buch.
Load hCoefStructure.
Load hOrderStructure.
Load hWfRO.
Inductive stable : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop := stable0 : forall P Q : list (poly A0 eqA ltM), (forall a : poly A0 eqA ltM, Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a P -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a Q) -> (forall a : poly A0 eqA ltM, Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a Q -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec a P) -> stable P Q.
Hint Resolve stable0 : core.
Hint Resolve (Cb_in _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os) : core.
Inductive reds : poly A0 eqA ltM -> poly A0 eqA ltM -> list (poly A0 eqA ltM) -> Prop := | reds0 : forall (P : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a b) P -> reds a b P | reds1 : forall (P : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM), In c P -> reds a c P -> reds c b P -> divp A A0 eqA multA divA n ltM (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) c -> reds a b P.
Inductive cpRes : Set := | Keep : forall P : list (poly A0 eqA ltM), cpRes | DontKeep : forall P : list (poly A0 eqA ltM), cpRes.
Definition getRes : cpRes -> list (poly A0 eqA ltM).
intros H'; case H'; auto.
Defined.
Definition addRes : poly A0 eqA ltM -> cpRes -> cpRes.
intros i H'; case H'.
intros H'0; exact (Keep (i :: H'0)).
intros H'0; exact (DontKeep (i :: H'0)).
Defined.
Definition slice : poly A0 eqA ltM -> poly A0 eqA ltM -> list (poly A0 eqA ltM) -> cpRes.
intros i a q; elim q; clear q.
case (foreigner_dec A A0 A1 eqA multA n ltM i a).
intros H; exact (DontKeep nil).
intros H; exact (Keep nil).
intros b q1 Rec.
case (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i a) b).
intros divp10; exact (DontKeep (b :: q1)).
intros divp10.
case (divp_dec _ _ _ _ _ _ _ _ _ cs n ltM (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM i b) a).
intros divp11; exact Rec.
intros divp11; exact (addRes b Rec).
Defined.
Definition slicef : poly A0 eqA ltM -> poly A0 eqA ltM -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros i a q; case (slice i a q); auto.
Defined.
Definition Tl : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop.
exact (fun x y : list (poly A0 eqA ltM) => length x < length y).
Defined.
Scheme Sdep := Induction for prod Sort Prop.
Inductive genPcP : poly A0 eqA ltM -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop := | genPcP0 : forall (i : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)), genPcP i nil L L | genPcP1 : forall (L L1 L2 L3 : list _) (a i : poly A0 eqA ltM), slice i a L1 = Keep L2 -> genPcP i L2 L L3 -> genPcP i (a :: L1) L (addEnd A A0 eqA n ltM (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os i a) L3) | genPcP2 : forall (L L1 L2 L3 : list _) (a i : poly A0 eqA ltM), slice i a L1 = DontKeep L2 -> genPcP i L2 L L3 -> genPcP i (a :: L1) L L3.
Hint Resolve genPcP0 : core.
Hint Resolve (addEnd_id2 A A0 eqA n ltM) : core.
Hint Resolve (addEnd_id1 A A0 eqA n ltM) : core.
Definition genPcPf0 : forall (i : poly A0 eqA ltM) (aP R : list (poly A0 eqA ltM)), {Q : list (poly A0 eqA ltM) | genPcP i aP R Q}.
intros i aP; pattern aP in |- *.
apply well_founded_induction with (A := list (poly A0 eqA ltM)) (R := Tl); clear aP; auto.
try exact wf_Tl.
intros aP; case aP.
intros H' R; exists R; auto.
intros a L1 Rec L; generalize (refl_equal (slice i a L1)); pattern (slice i a L1) at 2 in |- *; case (slice i a L1).
intros L2 H'.
lapply (Rec L2); [ intros H'1; elim (H'1 L); intros L3 E | idtac ]; auto.
exists (addEnd A A0 eqA n ltM (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os i a) L3); auto.
apply genPcP1 with (L2 := L2); auto.
generalize (slice_Tl i a L1); unfold slicef in |- *; rewrite H'; simpl in |- *; auto.
intros L2 H'.
lapply (Rec L2); [ intros H'1; elim (H'1 L); intros L3 E | idtac ]; auto.
exists L3; auto.
apply genPcP2 with (L2 := L2); auto.
generalize (slice_Tl i a L1); unfold slicef in |- *; rewrite H'; simpl in |- *; auto.
Definition genPcPf : poly A0 eqA ltM -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros i aP Q; case (genPcPf0 i aP Q).
intros x H'; exact x.
Defined.
Hint Resolve genPcPf_incl : core.
Definition genOCPf : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros H'; elim H'.
exact (nil (A:=poly A0 eqA ltM)).
intros a l rec; exact (genPcPf a l rec).
Defined.
Inductive OBuch : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop := | OBuch0 : forall aL : list (poly A0 eqA ltM), OBuch aL nil aL | OBuch1 : forall (a : poly A0 eqA ltM) (aP Q R : list (poly A0 eqA ltM)), OBuch (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP) (genPcPf (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP Q) R -> ~ BuchAux.zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) -> OBuch aP (a :: Q) R | OBuch2 : forall (a : poly A0 eqA ltM) (aP Q R : list (poly A0 eqA ltM)), OBuch aP Q R -> BuchAux.zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) -> OBuch aP (a :: Q) R.
Hint Resolve OBuch0 OBuch2 : core.
Hint Resolve incl_refl incl_tl : core.
Inductive redIn : poly A0 eqA ltM -> poly A0 eqA ltM -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop := | redIn0b : forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), redIn b a P Q R -> redIn a b P Q R | redIn0 : forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a b) Q -> redIn a b P Q R | redIn1 : forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a b) R -> redIn a b P Q R | redIn2 : forall (P Q R : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM), In c P -> redIn a c P Q R -> redIn b c P Q R -> divp A A0 eqA multA divA n ltM (ppcp A A0 A1 eqA plusA invA minusA multA divA cs n ltM a b) c -> redIn a b P Q R.
Hint Resolve redIn1 redIn0 : core.
Remark lem_redIn_nil : forall (aP Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a R -> In b R -> redIn a b aP Q R -> Q = nil -> aP = R -> reds a b R.
intros aP Q R a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4 H'5.
apply reds_com; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4.
rewrite H'3 in H'2; elim H'2.
intros P Q0 R0 a0 b0 H'2 H'3 H'4; rewrite <- H'4.
rewrite H'4.
apply reds0; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 H'8 H'9.
apply reds1 with (c := c); auto.
rewrite <- H'9; auto.
apply reds_com; auto.
Remark lem_redln_cons : forall (aP R Q : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a aP -> In b aP -> redIn a b aP Q R -> forall (c : poly A0 eqA ltM) (Q1 : list (poly A0 eqA ltM)), Q = c :: Q1 -> red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c R -> redIn a b aP Q1 R.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
apply H'3 with (c := c); auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'3 in H'2; elim H'2; auto.
intros H'5; rewrite H'5 in H'4; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
apply redIn2 with (c := c); auto.
apply H'4 with (c0 := c0); auto.
apply H'6 with (c0 := c0); auto.
Remark lem_redln_cons_gen : forall (aP R Q : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a aP -> In b aP -> redIn a b aP Q R -> forall (c : poly A0 eqA ltM) (Q1 : list (poly A0 eqA ltM)), incl (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c aP) aP) R -> Q = c :: Q1 -> redIn a b (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c aP) aP) Q1 R.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'4 in H'2; elim H'2; auto.
intros H'5; rewrite H'5.
apply redIn1; auto.
apply nf_red with (aP := P) (cs := cs) (os := os); auto.
apply incl_tran with (m := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c P :: P); simpl in |- *; auto.
apply incl_addEnd1; auto.
apply red_cons with (1 := cs); auto.
apply in_incl with (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c P :: P); auto.
apply incl_addEnd1; auto.
rewrite H'5; simpl in |- *; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
apply redIn2 with (c := c); auto.
Hint Resolve redln_cons_gen : core.
Let FPset (A : list (poly A0 eqA ltM)) := list (poly A0 eqA ltM).
Definition Fl : forall x : list (poly A0 eqA ltM), FPset x -> FPset x -> Prop.
unfold FPset in |- *; simpl in |- *.
intros H' P1 P2.
exact (Tl P1 P2).
Defined.
Let Co := lexprod (list (poly A0 eqA ltM)) FPset (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os) Fl.
Definition PtoS : list (poly A0 eqA ltM) * list (poly A0 eqA ltM) -> sigT FPset.
intros H'; case H'.
intros P1 P2.
exact (existT FPset P1 P2).
Defined.
Definition RL (x y : list (poly A0 eqA ltM) * list (poly A0 eqA ltM)) : Prop := Co (PtoS x) (PtoS y).
Definition pbuchf : forall PQ : list (poly A0 eqA ltM) * list (poly A0 eqA ltM), {R : list (poly A0 eqA ltM) | OBuch (fst PQ) (snd PQ) R}.
intros pq; pattern pq in |- *.
apply well_founded_induction with (A := (list (poly A0 eqA ltM) * list (poly A0 eqA ltM))%type) (R := RL).
try exact wf_RL.
intros x; elim x.
intros P Q; case Q; simpl in |- *.
intros H'; exists P; auto.
intros a Q2 Rec.
apply LetP with (A := poly A0 eqA ltM) (h := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P).
intros a0 H'.
case (zerop_dec A A0 eqA n ltM a0); intros red10.
elim (Rec (P, Q2)); simpl in |- *; [ intros R E | idtac ]; auto.
exists R; auto.
apply OBuch2; auto.
rewrite <- H'; auto.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply (right_lex _ _ (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os) Fl); auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim (Rec (addEnd A A0 eqA n ltM a0 P, genPcPf a0 P Q2)); simpl in |- *; [ intros R E0; try exact E0 | idtac ].
exists R; auto.
apply OBuch1; auto.
rewrite <- H'; auto.
rewrite <- H'; auto.
rewrite H'.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply (left_lex _ _ (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os) Fl); auto.
apply RO_lem; auto.
rewrite <- H'; auto.
Defined.
Definition strip : forall P : list (poly A0 eqA ltM) -> Prop, sig P -> list (poly A0 eqA ltM).
intros P H'; case H'.
intros x H'0; try assumption.
Defined.
Definition buch : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros P; exact (strip _ (pbuchf (P, genOCPf P))).
Defined.
End Buch.

Remark lem_redIn_nil : forall (aP Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a R -> In b R -> redIn a b aP Q R -> Q = nil -> aP = R -> reds a b R.
intros aP Q R a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4 H'5.
apply reds_com; auto.
intros P Q0 R0 a0 b0 H'2 H'3 H'4.
rewrite H'3 in H'2; elim H'2.
intros P Q0 R0 a0 b0 H'2 H'3 H'4; rewrite <- H'4.
rewrite H'4.
apply reds0; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 H'8 H'9.
apply reds1 with (c := c); auto.
rewrite <- H'9; auto.
Admitted.

Theorem redIn_nil : forall (R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a R -> In b R -> redIn a b R nil R -> reds a b R.
intros R a b H' H'0 H'1.
Admitted.

Remark lem_redln_cons : forall (aP R Q : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a aP -> In b aP -> redIn a b aP Q R -> forall (c : poly A0 eqA ltM) (Q1 : list (poly A0 eqA ltM)), Q = c :: Q1 -> red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c R -> redIn a b aP Q1 R.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
apply H'3 with (c := c); auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'3 in H'2; elim H'2; auto.
intros H'5; rewrite H'5 in H'4; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
apply redIn2 with (c := c); auto.
apply H'4 with (c0 := c0); auto.
Admitted.

Theorem redln_cons : forall (aP R Q : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM), In a aP -> In b aP -> redIn a b aP (c :: Q) R -> red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c R -> redIn a b aP Q R.
intros aP R Q a b c H' H'0 H'1 H'2; try assumption.
Admitted.

Theorem redInclP : forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), redIn a b P Q R -> forall P1 : list (poly A0 eqA ltM), incl P P1 -> redIn a b P1 Q R.
intros P Q R a b H'; elim H'; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 P1 H'2.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 Q1 H'6.
Admitted.

Theorem redInInclQ : forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), redIn a b P Q R -> forall Q1 : list (poly A0 eqA ltM), incl Q Q1 -> redIn a b P Q1 R.
intros P Q R a b H'; elim H'; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 Q1 H'2; try assumption.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 Q1 H'6; try assumption.
Admitted.

Theorem redInclR : forall (P Q R : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), redIn a b P Q R -> forall R1 : list (poly A0 eqA ltM), incl R R1 -> redIn a b P Q R1.
intros P Q R a b H'; elim H'; simpl in |- *; auto.
intros P0 Q0 R0 a0 b0 H'0 H'1 R1 H'2; try assumption.
apply redIn0b; auto.
intros P0 Q0 R0 a0 b0 H'0 R1 H'1; try assumption.
apply redIn1; auto.
apply red_incl with (1 := cs) (p := R0); auto.
intros P0 Q0 R0 a0 b0 c H'0 H'1 H'2 H'3 H'4 H'5 R1 H'6.
Admitted.

Remark lem_redln_cons_gen : forall (aP R Q : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a aP -> In b aP -> redIn a b aP Q R -> forall (c : poly A0 eqA ltM) (Q1 : list (poly A0 eqA ltM)), incl (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c aP) aP) R -> Q = c :: Q1 -> redIn a b (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c aP) aP) Q1 R.
intros aP R Q a b H' H'0 H'1; elim H'1; auto.
intros P Q0 R0 a0 b0 H'2 H'3 c Q1 H'4 H'5.
apply redIn0b; auto.
intros P Q0 R0 a0 b0 H'2 c Q1 H'3 H'4.
rewrite H'4 in H'2; elim H'2; auto.
intros H'5; rewrite H'5.
apply redIn1; auto.
apply nf_red with (aP := P) (cs := cs) (os := os); auto.
apply incl_tran with (m := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c P :: P); simpl in |- *; auto.
apply incl_addEnd1; auto.
apply red_cons with (1 := cs); auto.
apply in_incl with (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c P :: P); auto.
apply incl_addEnd1; auto.
rewrite H'5; simpl in |- *; auto.
intros P Q0 R0 a0 b0 c H'2 H'3 H'4 H'5 H'6 H'7 c0 Q1 H'8 H'9.
Admitted.

Theorem redln_cons_gen : forall (aP R Q : list (poly A0 eqA ltM)) (a b c : poly A0 eqA ltM), In a aP -> In b aP -> redIn a b aP (c :: Q) R -> incl (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c aP) aP) R -> redIn a b (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os c aP) aP) Q R.
intros aP R Q a b c H' H'0 H'1 H'2.
Admitted.

Theorem red_gen_in : forall (a : poly A0 eqA ltM) (aP R Q : list (poly A0 eqA ltM)), ~ BuchAux.zerop A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) -> OBuch (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP) (genPcPf (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP Q) R -> (forall b c : poly A0 eqA ltM, In b aP -> In c aP -> redIn b c aP (a :: Q) R) -> forall b : poly A0 eqA ltM, In b aP -> ~ BuchAux.zerop A A0 eqA n ltM b -> redIn (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) b (addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP) (genPcPf (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP Q) R.
intros a aP R Q H' H'0 H'1 b H'2 H'3.
lapply (spolyp_addEnd_genPcPf aP); [ intros H'5; elim (H'5 Q (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) b); [ intros c E; elim E; intros H'12 H'13; elim H'13; intros H'14 H'15; elim H'14; [ intros H'16; clear H'14 H'13 E | intros H'16; clear H'14 H'13 E ] | idtac | idtac | idtac ] | idtac ]; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redln_cons_gen; auto.
apply redInInclQ with (Q := a :: Q); auto with datatypes.
apply ObuchPincl with (Q := genPcPf (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP Q); auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redIn1.
apply red_incl with (p := addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP) (1 := cs); auto.
apply ObuchPincl with (Q := genPcPf (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP) aP Q); auto.
apply redln_cons_gen; auto.
apply redInInclQ with (Q := a :: Q); auto with datatypes.
Admitted.

Theorem OBuch_Inv : forall aP R Q : list (poly A0 eqA ltM), OBuch aP Q R -> (forall a b : poly A0 eqA ltM, In a aP -> In b aP -> redIn a b aP Q R) -> forall a b : poly A0 eqA ltM, In a R -> In b R -> reds a b R.
intros aP R Q H'; elim H'; simpl in |- *; auto.
intros aL H'0 a b H'1 H'2; try assumption.
apply redIn_nil; auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 H'3 a0 b H'4 H'5.
apply H'1; auto.
intros a1 b0 H'6.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'6); auto.
intros H'7; rewrite <- H'7; auto.
intros H'8.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'8); auto.
intros H'9; rewrite <- H'9; auto.
apply redIn1; auto.
apply red_id; auto.
intros H'9.
case (zerop_dec A A0 eqA n ltM b0); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
rewrite H'7; auto.
apply red_gen_in; auto.
intros H'7 H'8.
case (addEnd_cons A A0 eqA n ltM) with (1 := H'8); auto.
intros H'9; rewrite <- H'9; auto.
apply redIn0b.
case (zerop_dec A A0 eqA n ltM a1); intros Z.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
rewrite H'9.
apply red_gen_in; auto.
intros H'9.
apply redln_cons with (c := a); simpl in |- *; auto.
apply redInclP with (P := aP0); auto.
apply redInInclQ with (Q := a :: Q0); auto with datatypes.
unfold incl in |- *; auto.
apply nf_red with (aP := aP0) (cs := cs) (os := os); auto.
apply incl_tran with (m := addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP0) aP0); auto.
unfold incl in |- *; auto.
apply ObuchPincl with (Q := genPcPf (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP0) aP0 Q0); auto.
apply red_cons with (1 := cs); auto.
apply in_incl with (p := addEnd A A0 eqA n ltM (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP0) aP0); simpl in |- *; auto.
apply ObuchPincl with (Q := genPcPf (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a aP0) aP0 Q0); auto.
intros a aP0 Q0 R0 H'0 H'1 H'2 H'3 a0 b H'4 H'5.
apply H'1; auto.
intros a1 b0 H'6 H'7.
apply redln_cons with (c := a); auto.
apply red_incl with (p := aP0) (1 := cs); auto.
apply ObuchPincl with (Q := Q0); auto.
Admitted.

Theorem addEnd_incl : forall (a : poly A0 eqA ltM) (L1 L2 : list (poly A0 eqA ltM)), incl (a :: L1) L2 -> incl (addEnd A A0 eqA n ltM a L1) L2.
unfold incl in |- *; simpl in |- *; auto.
intros a L1 L2 H' a0 H'0.
Admitted.

Theorem genOCp_redln : forall aL1 R : list (poly A0 eqA ltM), incl aL1 R -> forall a b : poly A0 eqA ltM, In a aL1 -> In b aL1 -> redIn a b aL1 (genOCPf aL1) R.
intros aL1; elim aL1; simpl in |- *; auto.
intros a l H' R H'0 a0 b H'1 H'2.
elim H'2; [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; auto.
elim H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
apply redIn1; auto.
apply red_id; auto.
apply redIn0b.
case (zerop_dec A A0 eqA n ltM a); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_l; auto.
case (zerop_dec A A0 eqA n ltM a0); intros Z1; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
lapply (spolyp_addEnd_genPcPf l); [ intros H'4; elim (H'4 (genOCPf l) a a0); [ intros c E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14; elim H'13; [ intros H'15; clear H'13 H'12 E | intros H'15; clear H'13 H'12 E ] | idtac | idtac | idtac ] | idtac ]; auto.
apply redIn2 with (c := c); auto.
simpl in |- *; auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply redInclP with (P := l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); simpl in |- *; auto.
apply redIn2 with (c := c); auto.
simpl in |- *; auto.
apply redIn1; auto.
apply red_incl with (p := addEnd A A0 eqA n ltM a l) (1 := cs); auto.
apply addEnd_incl; auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
elim H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
case (zerop_dec A A0 eqA n ltM a); intros Z; auto.
apply redIn1; auto.
apply zerop_red_spoly_l; auto.
case (zerop_dec A A0 eqA n ltM b); intros Z1; auto.
apply redIn1; auto.
apply zerop_red_spoly_r; auto.
lapply (spolyp_addEnd_genPcPf l); [ intros H'4; elim (H'4 (genOCPf l) a b); [ intros c E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14; elim H'13; [ intros H'15; clear H'13 H'12 E | intros H'15; clear H'13 H'12 E ] | idtac | idtac | idtac ] | idtac ]; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply redInclP with (P := l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); simpl in |- *; auto.
apply redIn2 with (c := c); simpl in |- *; auto.
apply redIn1; auto.
apply red_incl with (1 := cs) (p := addEnd A A0 eqA n ltM a l); auto.
apply addEnd_incl; auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
apply incl_tran with (m := a :: l); auto.
apply redInclP with (P := l); auto.
apply redInInclQ with (Q := genOCPf l); auto.
apply H'; auto.
Admitted.

Theorem OBuch_Stable_f : forall P Q : list (poly A0 eqA ltM), OBuch P (genOCPf P) Q -> stable P Q.
intros P Q H'; try assumption.
apply OBuch_Stable with (Q := genOCPf P); auto.
intros a H'0; try assumption.
Admitted.

Theorem OBuch_Inv_f : forall P Q : list (poly A0 eqA ltM), OBuch P (genOCPf P) Q -> forall a b : poly A0 eqA ltM, In a Q -> In b Q -> reds a b Q.
intros P Q H' a b H'0 H'1; try assumption.
apply OBuch_Inv with (aP := P) (Q := genOCPf P); auto.
intros a0 b0 H'3 H'4.
apply genOCp_redln; auto.
Admitted.

Definition Fl : forall x : list (poly A0 eqA ltM), FPset x -> FPset x -> Prop.
unfold FPset in |- *; simpl in |- *.
intros H' P1 P2.
Admitted.

Theorem wf_Fl : forall x : list (poly A0 eqA ltM), well_founded (Fl x).
unfold FPset in |- *; simpl in |- *.
Admitted.

Theorem wf_Co : well_founded Co.
unfold Co in |- *; apply wf_lexprod.
apply wf_incl.
Admitted.

Definition PtoS : list (poly A0 eqA ltM) * list (poly A0 eqA ltM) -> sigT FPset.
intros H'; case H'.
intros P1 P2.
Admitted.

Theorem wf_RL : well_founded RL.
apply (wf_inverse_image _ _ Co PtoS); auto.
Admitted.

Definition strip : forall P : list (poly A0 eqA ltM) -> Prop, sig P -> list (poly A0 eqA ltM).
intros P H'; case H'.
Admitted.

Theorem pbuchf_Stable : forall P R : list (poly A0 eqA ltM), R = strip _ (pbuchf (P, genOCPf P)) -> stable P R.
simpl in |- *.
intros P R H'; try assumption.
apply OBuch_Stable_f; auto.
rewrite H'.
Admitted.

Theorem pbuchf_Inv : forall P R : list (poly A0 eqA ltM), R = strip _ (pbuchf (P, genOCPf P)) -> forall a b : poly A0 eqA ltM, In a R -> In b R -> reds a b R.
intros P R H' a b H'0 H'1; simpl in |- *.
apply OBuch_Inv_f with (P := P); auto.
rewrite H'; simpl in |- *; auto.
Admitted.

Definition buch : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
Admitted.

Theorem buch_Stable : forall P : list (poly A0 eqA ltM), stable P (buch P).
Admitted.

Theorem buch_reds : forall (P : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), In a (buch P) -> In b (buch P) -> reds a b (buch P).
intros P a b H' H'0.
Admitted.

Theorem reds_SpolyQ : forall (P : list (poly A0 eqA ltM)) (a b : poly A0 eqA ltM), reds a b P -> Spoly_1 A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b).
intros P a b H'; elim H'; auto.
intros P0 a0 b0 H'0; cut (red A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (spolyp A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os b0 a0) P0); auto.
case a0; case b0; unfold red in |- *; simpl in |- *; auto.
intros x H'1 x0 H'2 H'3; inversion H'3.
apply Spoly_10 with (Cp := H'2) (Cq := H'1); auto.
apply red_com; auto.
intros P0 a0 b0 c.
case c; case b0; case a0; simpl in |- *.
intros x; case x; simpl in |- *; auto.
intros c0 x0 c1 x1 c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a1 l c0 x0; case x0; simpl in |- *.
intros c1 x1 c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a2 l0 c1 x1; case x1; simpl in |- *.
intros c2 H'0 H'1 H'2 H'3 H'4 H'5; elim H'5.
intros a3 l1 c2 H'0 H'1 H'2 H'3 H'4 H'5.
change (Spoly_1 A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P0 (pX a1 l) (pX a2 l0)) in |- *.
apply Spoly_11 with (d := a3) (t := l1); auto.
change (inPolySet A A0 eqA n ltM (s2p A A0 eqA n ltM (mks A A0 eqA n ltM (pX a3 l1) c2)) P0) in |- *.
apply in_inPolySet; simpl in |- *; auto.
Admitted.

Theorem imp_in : forall (P : list (poly A0 eqA ltM)) (a : list (Term A n)), inPolySet A A0 eqA n ltM a P -> exists b : poly A0 eqA ltM, In b P /\ a = s2p A A0 eqA n ltM b.
intros P a H'; elim H'; auto.
intros a0 p H P0; exists (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) (pX a0 p) H); split; auto.
simpl in |- *; auto.
intros a0 p P0 H'0 H'1; elim H'1; intros b E; elim E; intros H'2 H'3; clear E H'1; auto.
Admitted.

Theorem reds_SpolyQ1 : forall P : list (poly A0 eqA ltM), (forall a b : poly A0 eqA ltM, In a P -> In b P -> reds a b P) -> SpolyQ A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P.
intros P H'.
apply SpolyQ0; auto.
intros p q H'0 H'1 H'2 H'3.
elim (imp_in P p); [ intros b E; elim E; intros H'7 H'8; clear E | idtac ]; auto.
rewrite H'8.
elim (imp_in P q); [ intros b0 E; elim E; intros H'9 H'10; clear E | idtac ]; auto.
rewrite H'10.
Admitted.

Theorem buch_spolyQ : forall P : list (poly A0 eqA ltM), SpolyQ A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec (buch P).
intros P.
apply reds_SpolyQ1; auto.
Admitted.

Theorem buch_Grobner : forall P : list (poly A0 eqA ltM), Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec (buch P).
intros P.
apply ConfluentReduce_imp_Grobner; auto.
apply SpolyQ_imp_ConfluentReduce with (1 := cs); auto.
Admitted.

Definition pbuchf : forall PQ : list (poly A0 eqA ltM) * list (poly A0 eqA ltM), {R : list (poly A0 eqA ltM) | OBuch (fst PQ) (snd PQ) R}.
intros pq; pattern pq in |- *.
apply well_founded_induction with (A := (list (poly A0 eqA ltM) * list (poly A0 eqA ltM))%type) (R := RL).
try exact wf_RL.
intros x; elim x.
intros P Q; case Q; simpl in |- *.
intros H'; exists P; auto.
intros a Q2 Rec.
apply LetP with (A := poly A0 eqA ltM) (h := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a P).
intros a0 H'.
case (zerop_dec A A0 eqA n ltM a0); intros red10.
elim (Rec (P, Q2)); simpl in |- *; [ intros R E | idtac ]; auto.
exists R; auto.
apply OBuch2; auto.
rewrite <- H'; auto.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply (right_lex _ _ (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os) Fl); auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim (Rec (addEnd A A0 eqA n ltM a0 P, genPcPf a0 P Q2)); simpl in |- *; [ intros R E0; try exact E0 | idtac ].
exists R; auto.
apply OBuch1; auto.
rewrite <- H'; auto.
rewrite <- H'; auto.
rewrite H'.
red in |- *; unfold Co in |- *; unfold PtoS in |- *.
apply (left_lex _ _ (RO A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os) Fl); auto.
apply RO_lem; auto.
rewrite <- H'; auto.
