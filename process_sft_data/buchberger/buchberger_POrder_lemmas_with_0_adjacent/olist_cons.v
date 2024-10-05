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

Theorem olist_cons : forall (l : list _) a b, ltT b a -> olist (pX b l) -> olist (pX a (pX b l)).
intros l; pattern l in |- *; apply (rev_ind (A:=Term A n)); auto.
intros x l0; case l0.
simpl in |- *.
unfold olist in |- *; simpl in |- *.
intros H' a b H'0 H'1; try assumption.
apply (d_conc _ ltM (T2M x) (T2M b) (consA (T2M a) nilA)).
generalize (olist_ltT pO); unfold ltT, olist in |- *; simpl in |- *; auto.
apply (olistOne a b); auto.
intros b l1 H' a b0 H'0; generalize H'; pattern l1 in |- *; apply (rev_ind (A:=Term A n)); unfold ltT, olist in |- *; simpl in |- *; auto.
intros H'2 H'3.
apply (d_conc _ ltM (T2M x) (T2M b) (consA (T2M a) (consA (T2M b0) nilA))); auto.
generalize (olist_ltT (b0 :: nil)); unfold ltT, olist in |- *; simpl in |- *; auto.
simpl in |- *; apply H'2; auto.
apply (desc_prefix _ ltM (consA (T2M b0) (consA (T2M b) nilA)) (T2M x)); auto.
intros x1 l2; rewrite (fP_app (l2 ++ x1 :: nil) (x :: nil)); rewrite (fP_app l2 (x1 :: nil)); rewrite (fP_app l2 (x :: nil)).
intros H'2 H'3 H'4; apply (d_conc _ ltM (T2M x) (T2M x1) (consA (T2M a) (consA (T2M b0) (consA (T2M b) (fP l2))))).
generalize (olist_ltT (pX b0 (pX b l2))); unfold olist, ltT in |- *; intros H'5; apply H'5.
rewrite (fP_app (pX b0 (pX b l2)) (pX x1 (pX x pO))); simpl in |- *; auto.
generalize (app_ass (fP l2) (consA (T2M x1) nilA) (consA (T2M x) nilA)); simpl in |- *; auto; unfold consA in |- *.
intros H'6; rewrite <- H'6; simpl in |- *; auto.
simpl in |- *; apply H'3; auto; apply (desc_prefix _ ltM) with (a := T2M x); auto.
