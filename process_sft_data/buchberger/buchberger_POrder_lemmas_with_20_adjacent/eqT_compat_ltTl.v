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

Lemma ltT_eqT : forall a b c d : Term A n, eqT a b -> eqT c d -> ltT a c -> ltT b d.
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

Lemma app2_inv : forall (x y z t : mon n) (p : listA), (p ++ consA x nilA) ++ consA y nilA = consA z (consA t nilA) -> x = z /\ y = t.
intros x y z t p; case p; simpl in |- *; auto.
intros H'; injection H'; simpl in |- *; auto.
intros a l; case l; simpl in |- *; auto.
intros H'; discriminate H'.
intros a0 l0; case l0; simpl in |- *; auto.
intros H'; discriminate H'.
Admitted.

Theorem olist_ltT : forall (l : list (Term A n)) (a b : Term A n), olist (l ++ pX a (pX b pO)) -> ltT b a.
unfold ltT, olist in |- *; simpl in |- *; auto.
intros l a b.
rewrite (fP_app l (pX a (pX b pO))); simpl in |- *; auto.
intros H'.
elim (dist_Desc_concat _ ltM (fP l) (consA (T2M a) (consA (T2M b) nilA))); [ intros H'5 H'6; try exact H'6 | idtac ]; auto.
simple inversion H'6.
discriminate H.
discriminate H.
elim (app2_inv y x (T2M a) (T2M b) l0); [ intros H'8 H'9 | idtac ]; auto.
Admitted.

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
Admitted.

Lemma eqT_compat_ltTl : forall a b c : Term A n, eqT b c -> ltT b a -> ltT c a.
unfold eqT in |- *; unfold ltT in |- *; intros a b c H; rewrite H; auto.
