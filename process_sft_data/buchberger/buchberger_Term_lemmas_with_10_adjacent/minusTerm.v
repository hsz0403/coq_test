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

Theorem T1_nz : ~ zeroP T1.
simpl in |- *; auto.
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

Theorem eqTerm_minusTerm_plusTerm_invTerm : forall a b : Term, eqTerm (minusTerm a b) (plusTerm a (invTerm b)).
intros a b; case a; case b; simpl in |- *; auto.
split; auto.
Admitted.

Theorem minusTerm_eqT : forall m1 m2 : Term, eqT m1 m2 -> eqT (minusTerm m1 m2) m1.
Admitted.

Theorem zeroP_minusTerm : forall a : Term, zeroP (minusTerm a a).
intros a; apply zeroP_comp_eqTerm with (a := plusTerm a (invTerm a)); auto.
apply plusTerm_invTerm_zeroP; auto.
Admitted.

Theorem multTerm_zeroP_div : forall a b : Term, zeroP (multTerm a b) -> zeroP a \/ zeroP b.
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 H.
Admitted.

Theorem multTerm_minusTerm_dist_l : forall a b c : Term, eqT a b -> eqTerm (minusTerm (multTerm a c) (multTerm b c)) (multTerm (minusTerm a b) c).
intros a b c eqT1.
apply eqTerm_trans with (y := multTerm (plusTerm a (invTerm b)) c); auto.
apply eqTerm_trans with (y := plusTerm (multTerm a c) (multTerm (invTerm b) c)); auto.
apply eqTerm_trans with (y := plusTerm (multTerm a c) (invTerm (multTerm b c))); auto.
apply eqTerm_minusTerm_plusTerm_invTerm; auto.
apply eqTerm_plusTerm_comp; auto.
apply eqT_trans with (y := multTerm b c); auto.
apply multTerm_eqT; auto.
apply invTerm_eqT; auto.
apply multTerm_eqT; auto.
apply eqT_trans with (y := b); auto.
apply invTerm_eqT; auto.
apply eqTerm_refl; auto.
apply eqTerm_sym; apply mult_invTerm_com; auto.
apply multTerm_plusTerm_dist_l; auto.
apply eqTerm_multTerm_comp; auto.
apply eqTerm_sym; apply eqTerm_minusTerm_plusTerm_invTerm; auto.
Admitted.

Theorem nzeroP_multTerm : forall a b : Term, ~ zeroP a -> ~ zeroP b -> ~ zeroP (multTerm a b).
Admitted.

Definition minusTerm : Term -> Term -> Term.
intros H; case H; intros b2 c2 H'; case H'; intros b3 c3; exact (minusA b2 b3, c2).
