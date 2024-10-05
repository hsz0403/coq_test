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

Theorem ltT_trans : transitive (Term A n) ltT.
unfold transitive, ltT in |- *; auto.
Admitted.

Lemma eqT_compat_ltTr : forall a b c : Term A n, eqT b c -> ltT a b -> ltT a c.
Admitted.

Lemma eqT_compat_ltTl : forall a b c : Term A n, eqT b c -> ltT b a -> ltT c a.
Admitted.

Theorem eqT_dec : forall x y : Term A n, {eqT x y} + {~ eqT x y}.
intros x y; unfold eqT in |- *; simpl in |- *; auto.
Admitted.

Theorem ltT_dec : forall x y : Term A n, {ltT x y} + {ltT y x} + {eqT x y}.
Admitted.

Lemma ltT_not_eqT : forall x y : Term A n, eqT x y -> ~ ltT x y.
unfold eqT, ltT in |- *; simpl in |- *; intros x y H; rewrite H; auto.
Admitted.

Lemma eqT_not_ltT : forall x y : Term A n, ltT x y -> ~ eqT x y.
unfold eqT, ltT, not in |- *; simpl in |- *; intros x y H Q; absurd (ltM (T2M x) (T2M y)); auto; rewrite Q; auto.
Admitted.

Theorem ltT_not_refl : forall x : Term A n, ~ ltT x x.
Admitted.

Lemma ltT_not_ltT : forall x y : Term A n, ltT x y -> ~ ltT y x.
intros x y H'; red in |- *; intros H'0; absurd (ltT x x); auto.
Admitted.

Lemma ltT_eqTr : forall a b c : Term A n, eqT a b -> ltT a c -> ltT b c.
Admitted.

Lemma ltT_eqTl : forall a b c : Term A n, eqT a b -> ltT c a -> ltT c b.
Admitted.

Theorem multTerm_ltT_l : forall m1 m2 m3, ltT m1 m2 -> ltT (multTerm multA m3 m1) (multTerm multA m3 m2).
intros a b c; case a; case b; case c; unfold ltT in |- *; simpl in |- *; auto.
intros a0 m a1 m0 a2 m1 H.
Admitted.

Theorem multTerm_ltT_r : forall m1 m2 m3, ltT m1 m2 -> ltT (multTerm multA m1 m3) (multTerm multA m2 m3).
intros a b c; case a; case b; case c; unfold ltT in |- *; simpl in |- *; auto.
Admitted.

Theorem T1_is_min_ltT : forall a, ~ ltT a (T1 A1 n).
intros a; case a; unfold ltT in |- *; simpl in |- *; auto.
Admitted.

Theorem minusTerm_ltT_l : forall a b c, eqT a b -> ltT a c -> ltT (minusTerm minusA a b) c.
Admitted.

Theorem invTerm_ltT_l : forall a c, ltT a c -> ltT (invTerm invA a) c.
Admitted.

Theorem fP_app : forall p q : list (Term A n), fP (p ++ q) = fP p ++ fP q.
intros p; elim p; simpl in |- *; auto.
intros a l H' q.
Admitted.

Theorem olistOne : forall a b : Term A n, ltT b a -> olist (pX a (pX b pO)).
unfold olist, ltT in |- *; simpl in |- *; auto.
intros a b H'.
Admitted.

Theorem olistO : olist pO.
unfold olist, ltT in |- *; simpl in |- *; auto.
Admitted.

Lemma ltT_eqT : forall a b c d : Term A n, eqT a b -> eqT c d -> ltT a c -> ltT b d.
unfold eqT, ltT in |- *; intros a b c d R1 R2; rewrite R1; rewrite R2; auto.
