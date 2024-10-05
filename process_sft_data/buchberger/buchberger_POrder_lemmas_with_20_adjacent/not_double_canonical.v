Require Import Lexicographic_Exponentiation.
Require Import Relation_Definitions.
Require Import Inverse_Image.
Require Import Inclusion.
Require Import List.
Require Import Relation_Operators.
Require Import Relation_Operators_compat.
Require Import Monomials.
Require Import Term.
Require Import CoefStructure.
Require Import OrderStructure.
Section Porder.
Load hCoefStructure.
Load hOrderStructure.
Load hTerm.
Set Implicit Arguments.
Unset Strict Implicit.
Definition ltT (a b : Term A n) : Prop := ltM (T2M a) (T2M b).
Hint Unfold ltT : core.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve ltT_not_eqT eqT_not_ltT ltT_not_refl : core.
Hint Resolve ltT_not_ltT : core.
Let eqT_refl := eqT_refl A n.
Set Implicit Arguments.
Unset Strict Implicit.
Definition pX := cons (A:=Term A n).
Set Strict Implicit.
Unset Implicit Arguments.
Definition pO := nil (A:=Term A n).
Let consA := cons (A:=mon n).
Let nilA := nil (A:=mon n).
Let listA := list (mon n).
Hint Unfold consA nilA listA : core.
Fixpoint fP (a : list (Term A n)) : listA := match a with | nil => nilA | b :: p => consA (T2M b) (fP p) end.
Let DescA := Desc (mon n) ltM.
Set Implicit Arguments.
Unset Strict Implicit.
Definition olist (p : list (Term A n)) := DescA (fP p).
Hint Resolve d_nil d_one : core.
Hint Unfold olist DescA : core.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve olistOne : core.
Set Implicit Arguments.
Unset Strict Implicit.
Inductive ltP : list (Term A n) -> list (Term A n) -> Prop := | ltPO : forall x p, ltP pO (pX x p) | ltP_hd : forall x y p q, ltT x y -> ltP (pX x p) (pX y q) | ltP_tl : forall x y p q, eqT x y -> ltP p q -> ltP (pX x p) (pX y q).
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve fltP : core.
Hint Resolve ltPO : core.
Hint Resolve ltP_order_comp : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition nZterm : list (Term A n) -> Prop.
intros H'; elim H'.
exact True.
intros a P1 Rec.
exact (Rec /\ ~ zeroP (A:=A) A0 eqA (n:=n) a).
Defined.
Definition canonical (a : list (Term A n)) : Prop := olist a /\ nZterm a.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve canonical_imp_olist : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition poly := {a : list _ | canonical a}.
Definition sltP (sa sb : poly) : Prop := let (p, H1) return Prop := sa in let (q, H2) return Prop := sb in ltP p q.
Definition fspoly (sa : poly) : Pow _ ltM := let (p, H) return (Pow _ ltM) := sa in exist DescA (fP p) (canonical_imp_olist p H).
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve fsltP : core.
End Porder.

Theorem olist_X : forall (l : list _) a, olist (pX a l) -> olist l.
intros l a H'.
Admitted.

Theorem olist_imp_olist : forall l a b, olist (pX a (pX b l)) -> olist (pX a l).
intros l; case l.
intros a b H'.
elim (dist_Desc_concat _ ltM (consA (T2M a) nilA) (consA (T2M b) nilA)); [ intros H'5 H'6 | idtac ]; auto.
intros b l0 a b0 H'.
apply olist_cons; auto.
apply ltT_trans with (y := b0).
apply olist_pX_order with (l := l0); auto.
apply olist_X with (a := a); auto.
apply olist_pX_order with (l := b :: l0); auto.
apply olist_X with (a := b0); auto.
Admitted.

Lemma fltP : forall p q, ltP p q -> Ltl _ ltM (fP p) (fP q).
intros p q H'; elim H'; auto.
simpl in |- *; intros; apply (Lt_nil (mon n)); auto.
simpl in |- *; intros; apply (Lt_hd (mon n)); auto.
simpl in |- *; unfold eqT in |- *; (intros x y p1 q1 H; rewrite H).
Admitted.

Theorem ltp_not_refl : forall x, ~ ltP x x.
intros x; elim x.
red in |- *; intros H'; inversion H'.
intros a l H'; red in |- *; intros H'0; simple inversion H'0.
discriminate H.
injection H1.
injection H0.
intros H'1 H'2 H'3 H'4; rewrite H'2; rewrite H'4; intros H'5.
apply (ltT_not_refl a); auto.
injection H1; injection H2.
Admitted.

Theorem ltP_trans : forall x y z, ltP x y -> ltP y z -> ltP x z.
intros x y z H'; generalize z; clear z; elim H'.
intros x0 p z; case z; auto.
intros H'0; inversion H'0.
intros x0 y0 p q H'0 z H'1; simple inversion H'1.
discriminate H.
rewrite <- H1.
intros H'2; try assumption.
apply ltP_hd; auto.
apply ltT_trans with (y := y0); auto.
injection H0.
intros H'3 H'4; rewrite <- H'4; auto.
rewrite <- H2.
intros H'2 H'3; apply ltP_hd; auto.
apply ltT_eqTl with (a := x1); auto.
injection H1.
intros H'4 H'5; rewrite H'5; auto.
intros x0 y0 p q H'0 H'1 H'2 z H'3; simple inversion H'3.
discriminate H.
rewrite <- H1; auto.
intros H'4; apply ltP_hd; auto.
apply ltT_eqTr with (a := y0).
apply (eqT_sym A n); auto.
injection H0.
intros H'5 H'6; rewrite <- H'6; auto.
rewrite <- H2.
intros H'4 H'5; apply ltP_tl; auto.
apply (eqT_trans A n) with (y := x1); auto.
injection H1.
intros H'6 H'7; rewrite H'7; auto.
apply H'2; auto.
injection H1.
Admitted.

Theorem olist_pX_ltP : forall a p, olist (pX a p) -> ltP p (pX a pO).
intros a p; case p; auto.
intros b l H'.
apply ltP_hd; auto.
Admitted.

Theorem ltP_pX_olist : forall a p, olist p -> ltP p (pX a pO) -> olist (pX a p).
intros a p; case p; auto.
intros H' H'1; unfold olist, DescA, consA in |- *; simpl in |- *; unfold consA, nilA in |- *.
apply d_one; auto.
intros b l H' H'0.
apply olist_cons; auto.
simple inversion H'0.
discriminate H.
injection H1; injection H0; intros H'1 H'2 H'3 H'4; (rewrite H'2; rewrite H'4); auto.
injection H2; intros H'1 H'2; rewrite H'1; auto.
Admitted.

Theorem ltP_order_comp : forall (a b c : Term A n) (p q : list (Term A n)), ltP (pX b p) (pX a q) -> ltT a c -> ltT b c.
intros a b c p q H1; inversion_clear H1.
intros; apply ltT_trans with (y := a); auto.
apply eqT_compat_ltTl.
Admitted.

Definition nZterm : list (Term A n) -> Prop.
intros H'; elim H'.
exact True.
intros a P1 Rec.
Admitted.

Theorem canonical_imp_olist : forall a, canonical a -> olist a.
Admitted.

Theorem canonical0 : forall a b, ltT b a -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> canonical (pX a (pX b pO)).
intros a b H' H'0 H'1; simpl in |- *; auto.
Admitted.

Theorem canonical_ltT : forall l a b, canonical (l ++ pX a (pX b pO)) -> ltT b a.
intros l a b H'; auto.
Admitted.

Theorem canonical_nzeroP : forall a p, canonical (pX a p) -> ~ zeroP (A:=A) A0 eqA (n:=n) a.
intros a p H'; red in |- *; intros H'0; inversion H'.
Admitted.

Theorem canonical_cons : forall l a b, ltT b a -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> canonical (pX b l) -> canonical (pX a (pX b l)).
intros l a b H' H'0 H'1; split; simpl in |- *; auto.
apply olist_cons; auto.
repeat split; auto.
inversion H'1; simpl in H0; intuition.
Admitted.

Theorem canonical_pX_eqT : forall a b p, canonical (pX a p) -> eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> canonical (pX b p).
intros a b p H' H'0 H'1.
split; auto.
apply olist_pX_eqT with (a := a); auto.
simpl in |- *; split; auto.
Admitted.

Theorem canonical_pX_order : forall l a b, canonical (pX a (pX b l)) -> ltT b a.
intros l a b H'; auto.
Admitted.

Theorem canonical_imp_canonical : forall l a, canonical (pX a l) -> canonical l.
intros l a H'.
split; auto.
apply olist_X with (a := a); auto.
Admitted.

Theorem canonical_skip_fst : forall l a b, canonical (pX a (pX b l)) -> canonical (pX a l).
intros l a b H'; split; auto.
apply olist_imp_olist with (b := b); auto.
inversion H'.
Admitted.

Theorem canonical_pX_ltP : forall a p, canonical (pX a p) -> ltP p (pX a pO).
intros a p H'; auto.
Admitted.

Theorem ltP_pX_canonical : forall a p, canonical p -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> ltP p (pX a pO) -> canonical (pX a p).
intros a p H' H'0 H'1; split; auto.
apply ltP_pX_olist; auto.
inversion H'.
Admitted.

Theorem canonical_imp_in_nzero : forall p : list (Term A n), canonical p -> forall a : Term A n, In a p -> ~ zeroP (A:=A) A0 eqA (n:=n) a.
intros p; elim p; auto.
intros a l H' H'0 a0 H'1; elim H'1; auto.
intros H'2; rewrite <- H'2.
apply canonical_nzeroP with (p := l); auto.
intros H'2; auto.
apply H'; auto.
Admitted.

Theorem fsltP : forall p q : poly, sltP p q -> lex_exp _ ltM (fspoly p) (fspoly q).
Admitted.

Theorem sltp_wf : well_founded sltP.
lapply (wf_inverse_image poly (Pow _ ltM) (lex_exp _ ltM) fspoly); [ intros H'3 | idtac ].
apply wf_incl with (R2 := fun x y : poly => lex_exp _ ltM (fspoly x) (fspoly y)); auto.
red in |- *; auto.
Admitted.

Theorem not_double_canonical : forall (a : Term A n) (p : list (Term A n)), ~ canonical (pX a (pX a p)).
intros a p; red in |- *; intros H'; try exact H'.
absurd (ltT a a); auto.
apply canonical_pX_order with (l := p); auto.
