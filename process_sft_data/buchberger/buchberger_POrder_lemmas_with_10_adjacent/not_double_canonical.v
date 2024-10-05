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
