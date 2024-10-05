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

Definition zeroP : Term -> Prop.
intros H'; case H'.
Admitted.

Definition eqTerm : Term -> Term -> Prop.
intros H'; case H'.
intros a a' H'2; case H'2.
Admitted.

Theorem eqTerm_refl : reflexive Term eqTerm.
red in |- *.
Admitted.

Theorem eqTerm_sym : symmetric Term eqTerm.
red in |- *.
intros x y; case x; case y; simpl in |- *; intuition.
Admitted.

Theorem eqTerm_trans : transitive Term eqTerm.
red in |- *.
intros x y z; case x; case y; case z; simpl in |- *; intuition.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := a0); auto.
Admitted.

Definition T2M : Term -> mon n.
Admitted.

Lemma eqT_refl : reflexive _ eqT.
Admitted.

Lemma eqT_sym : symmetric _ eqT.
Admitted.

Lemma eqT_trans : transitive _ eqT.
red in |- *; unfold eqT in |- *.
Admitted.

Theorem eqTerm_imp_eqT : forall a b : Term, eqTerm a b -> eqT a b.
Admitted.

Theorem eqTerm_dec : forall x y : Term, {eqTerm x y} + {~ eqTerm x y}.
intros x y; case x; case y; simpl in |- *.
intros b2 c2 b3 c3.
case (eqA_dec b3 b2); intros eqAZ; auto.
case (eqmon_dec n c3 c2); intros eqAZ1; auto.
right; red in |- *; intros H'; elim H'; intros H'0 H'1; clear H'; auto.
Admitted.

Theorem eqT_zerop_is_eqTerm : forall a b : Term, eqT a b -> zeroP a -> zeroP b -> eqTerm a b.
intros a b; case a; case b; simpl in |- *; auto.
intuition.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := A0); auto.
Admitted.

Theorem zeroP_dec : forall x : Term, {zeroP x} + {~ zeroP x}.
intros x; case x; simpl in |- *.
intros b H'.
Admitted.

Theorem zeroP_comp_eqTerm : forall a b : Term, zeroP a -> eqTerm a b -> zeroP b.
intros a b; case a; case b; simpl in |- *; auto.
intuition.
Admitted.

Theorem nzeroP_comp_eqTerm : forall a b : Term, ~ zeroP a -> eqTerm a b -> ~ zeroP b.
intros a b H' H'0; red in |- *; intros H'1.
apply H'.
apply zeroP_comp_eqTerm with (a := b); auto.
Admitted.

Definition plusTerm : Term -> Term -> Term.
Admitted.

Theorem zeroP_plusTermr : forall a b : Term, eqT a b -> zeroP b -> eqTerm a (plusTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 m1 a2 m2 H1 H2; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA a2 A0); auto.
Admitted.

Theorem zeroP_plusTerml : forall a b : Term, eqT a b -> zeroP a -> eqTerm b (plusTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 m1 a2 m2 H1 H2; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA A0 a1); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA a1 A0); auto.
Admitted.

Theorem plusTerm_comp_l : forall a b c : Term, eqT a c -> eqT b c -> eqTerm a b -> eqTerm (plusTerm a c) (plusTerm b c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
Admitted.

Theorem plusTerm_com : forall x y : Term, eqT x y -> eqTerm (plusTerm x y) (plusTerm y x).
Admitted.

Theorem plusTerm_eqT1 : forall m1 m2 : Term, eqT m1 m2 -> eqT (plusTerm m1 m2) m1.
Admitted.

Theorem plusTerm_eqT2 : forall m1 m2 : Term, eqT m1 m2 -> eqT (plusTerm m1 m2) m2.
Admitted.

Theorem plusTerm_assoc : forall a a0 A1 : Term, eqT A1 a0 -> eqT a a0 -> eqTerm (plusTerm (plusTerm A1 a0) a) (plusTerm A1 (plusTerm a0 a)).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intuition.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs).
Admitted.

Theorem eqTerm_plusTerm_comp : forall a b c d : Term, eqT a c -> eqT b d -> eqTerm a b -> eqTerm c d -> eqTerm (plusTerm a c) (plusTerm b d).
intros a b c d; case a; case b; case c; case d; simpl in |- *; auto.
Admitted.

Definition multTerm : Term -> Term -> Term.
Admitted.

Theorem zeroP_multTerm_l : forall a b : Term, zeroP a -> zeroP (multTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
Admitted.

Theorem zeroP_multTerm_r : forall a b : Term, zeroP a -> zeroP (multTerm b a).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 H' b2 H'0 H'1; apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA a1 A0); auto.
Admitted.

Theorem multTerm_plusTerm_dist_l : forall a b c : Term, eqTerm (plusTerm (multTerm a c) (multTerm b c)) (multTerm (plusTerm a b) c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a1 m1 a2 m2 a3 m3; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 a3) (multA a1 a2)); auto.
Admitted.

Theorem multTerm_plusTerm_dist_r : forall a b c : Term, eqTerm (plusTerm (multTerm c a) (multTerm c b)) (multTerm c (plusTerm a b)).
Admitted.

Theorem multTerm_eqT : forall a b c d : Term, eqT a b -> eqT c d -> eqT (multTerm a c) (multTerm b d).
intros a b c d; case a; case b; case c; case d; unfold eqT in |- *; simpl in |- *; auto.
Admitted.

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

Theorem plusTerm_comp_r : forall a b c : Term, eqT c a -> eqT c b -> eqTerm a b -> eqTerm (plusTerm c a) (plusTerm c b).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intuition.
