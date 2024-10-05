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

Theorem multTerm_assoc : forall a b c : Term, eqTerm (multTerm a (multTerm b c)) (multTerm (multTerm a b) c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a0 m a1 m0 a2 m1; split; auto.
apply multA_assoc with (1 := cs); auto.
Admitted.

Theorem multTerm_com : forall a b : Term, eqTerm (multTerm a b) (multTerm b a).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0; split; auto.
Admitted.

Theorem eqTerm_multTerm_comp : forall a b c d : Term, eqTerm a b -> eqTerm c d -> eqTerm (multTerm a c) (multTerm b d).
intros a b c d; case a; case b; case c; case d; simpl in |- *; auto.
intros a1 m1 a2 m2 a3 m3 a4 m4; intros H1; case H1; intros H2 H3 H4; case H4; intros H5 H6; split; auto.
Admitted.

Definition invTerm : Term -> Term.
Admitted.

Theorem plusTerm_invTerm_zeroP : forall a : Term, zeroP (plusTerm a (invTerm a)).
intros a; case a; simpl in |- *; auto.
Admitted.

Theorem zeroP_invTerm_zeroP : forall a : Term, zeroP a -> zeroP (invTerm a).
intros a; case a; simpl in |- *; auto.
intros b H' H'0; apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA A0 (invA A0)); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := invA A0); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA (invA A0) A0); auto.
Admitted.

Theorem invTerm_invol : forall a : Term, eqTerm a (invTerm (invTerm a)).
intros a; case a; simpl in |- *; auto.
intros a0 m; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA a0 A0); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA a0 (plusA (invA a0) (invA (invA a0)))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (plusA a0 (invA a0)) (invA (invA a0))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA A0 (invA (invA a0))); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (invA (invA a0)) A0); auto.
Admitted.

Theorem nZero_invTerm_nZero : forall a : Term, ~ zeroP a -> ~ zeroP (invTerm a).
intros a H'; red in |- *; intros H'0; absurd (zeroP a); auto.
apply zeroP_comp_eqTerm with (a := invTerm (invTerm a)); auto.
apply zeroP_invTerm_zeroP; auto.
Admitted.

Definition T1 : Term.
Admitted.

Theorem T1_nz : ~ zeroP T1.
simpl in |- *; auto.
Admitted.

Theorem T1_multTerm_r : forall a b : Term, eqTerm a T1 -> eqTerm b (multTerm b a).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 H'; elim H'; intros H'0 H'1; rewrite H'1; clear H'.
split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA a0 A1); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA A1 a0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); apply multA_A1_l with (1 := cs); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Admitted.

Theorem nZero_invTerm_T1 : ~ zeroP (invTerm T1).
apply nZero_invTerm_nZero; auto.
Admitted.

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
Admitted.

Theorem mult_invTerm_com_r : forall a b : Term, eqTerm (multTerm a (invTerm b)) (invTerm (multTerm a b)).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 (invA a0)) A0); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 (invA a0)) (plusA (multA a1 a0) (invA (multA a1 a0)))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (plusA (multA a1 (invA a0)) (multA a1 a0)) (invA (multA a1 a0))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 (plusA (invA a0) a0)) (invA (multA a1 a0))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 (plusA a0 (invA a0))) (invA (multA a1 a0))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 A0) (invA (multA a1 a0))); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA A0 a1) (invA (multA a1 a0))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA A0 (invA (multA a1 a0))); auto.
Admitted.

Theorem eqTerm_invTerm_comp : forall a b : Term, eqTerm a b -> eqTerm (invTerm a) (invTerm b).
intros a b; case a; case b; simpl in |- *; auto.
Admitted.

Theorem invTerm_eqT : forall a : Term, eqT a (invTerm a).
Admitted.

Theorem T1_eqT : forall a b : Term, eqTerm a T1 -> eqT b (multTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 m1 a2 m2 H1; case H1; intros H2 H3; auto.
rewrite H3; auto.
Admitted.

Theorem eqTerm_T1_eqT : forall a : Term, eqTerm a T1 -> eqT a T1.
intros a; case a; simpl in |- *; auto.
Admitted.

Definition minusTerm : Term -> Term -> Term.
Admitted.

Theorem eqTerm_minusTerm_plusTerm_invTerm : forall a b : Term, eqTerm (minusTerm a b) (plusTerm a (invTerm b)).
intros a b; case a; case b; simpl in |- *; auto.
split; auto.
Admitted.

Theorem T1_multTerm_l : forall a b : Term, eqTerm a T1 -> eqTerm b (multTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 H'; elim H'; intros H'0 H'1; rewrite H'1; clear H'; auto.
split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA A1 a0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs).
apply multA_A1_l with (1 := cs); auto.
apply multA_eqA_comp with (1 := cs); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply sym_eq; unfold M1 in |- *; apply mult_mon_zero_l.
