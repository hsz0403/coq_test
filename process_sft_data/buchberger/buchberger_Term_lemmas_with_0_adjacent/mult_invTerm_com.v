Require Import Relation_Definitions.
Require Import CoefStructure.
Require Import moreCoefStructure.
Require Import OrderStructure.
Require Import Monomials.
Section Term.
Load hCoefStructure.
Load mCoefStructure.
Load hOrderStructure.
Load mOrderStructure.
Definition M1 := zero_mon n.
Definition Term := (A * mon n)%type.
Set Implicit Arguments.
Unset Strict Implicit.
Definition zeroP : Term -> Prop.
intros H'; case H'.
intros a H'1; exact (eqA a A0).
Defined.
Definition eqTerm : Term -> Term -> Prop.
intros H'; case H'.
intros a a' H'2; case H'2.
intros b b'; exact (eqA a b /\ a' = b').
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Set Implicit Arguments.
Unset Strict Implicit.
Definition T2M : Term -> mon n.
intros t; case t; intros a m; exact m.
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Set Implicit Arguments.
Unset Strict Implicit.
Definition eqT (a b : Term) : Prop := T2M a = T2M b.
Hint Unfold eqT : core.
Set Strict Implicit.
Unset Implicit Arguments.
Set Implicit Arguments.
Unset Strict Implicit.
Definition plusTerm : Term -> Term -> Term.
intros x; case x; intros b2 c2; intros y; case y; intros b3 c3; exact (plusA b2 b3, c2).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve eqTerm_plusTerm_comp : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition multTerm : Term -> Term -> Term.
intros H'; case H'; intros b2 c2 H1'; case H1'; intros b3 c3; exact (multA b2 b3, mult_mon n c2 c3).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve eqTerm_multTerm_comp : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition invTerm : Term -> Term.
intros H; case H; intros b2 c2; exact (invA b2, c2).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve nZero_invTerm_nZero : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition T1 : Term.
exact (A1, M1).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve nZero_invTerm_T1 : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition minusTerm : Term -> Term -> Term.
intros H; case H; intros b2 c2 H'; case H'; intros b3 c3; exact (minusA b2 b3, c2).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve multTerm_minusTerm_dist_l : core.
End Term.

Theorem mult_invTerm_com : forall a b : Term, eqTerm (multTerm (invTerm a) b) (invTerm (multTerm a b)).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA (invA a1) a0) A0); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA (invA a1) a0) (plusA (multA a1 a0) (invA (multA a1 a0)))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (plusA (multA (invA a1) a0) (multA a1 a0)) (invA (multA a1 a0))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA (plusA (invA a1) a1) a0) (invA (multA a1 a0))); auto.
apply plusA_eqA_comp with (1 := cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a0 (invA a1)) (multA a0 a1)); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (multA a0 (plusA (invA a1) a1)); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA (plusA a1 (invA a1)) a0) (invA (multA a1 a0))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA A0 a0) (invA (multA a1 a0))); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA A0 (invA (multA a1 a0))); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (invA (multA a1 a0)) A0); auto.
