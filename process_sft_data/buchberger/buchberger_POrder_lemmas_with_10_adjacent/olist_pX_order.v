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

Lemma fp_tail : forall x p, fP (p ++ x :: nil) = fP p ++ T2M x :: nil.
intros x p; elim p; simpl in |- *; auto.
Admitted.

Lemma descA_subst : forall a b : listA, b = a -> DescA a -> DescA b.
Admitted.

Theorem olist_pX_eqT : forall a b p, olist (pX a p) -> eqT a b -> olist (pX b p).
unfold olist, eqT in |- *.
simpl in |- *; auto.
Admitted.

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

Theorem olist_pX_order : forall l a b, olist (pX a (pX b l)) -> ltT b a.
intros l a b H'.
elim (dist_Desc_concat _ ltM (consA (T2M a) (consA (T2M b) nilA)) (fP l)); [ intros H'5 H'6 | idtac ]; auto.
apply olist_ltT with (l := pO); auto.
