Require Import Relation_Definitions.
Require Import CoefStructure.
Require Import moreCoefStructure.
Require Import OrderStructure.
Require Import Monomials.
Require Import Term.
Require Import List.
Section DivTerm.
Load hCoefStructure.
Load mCoefStructure.
Load hOrderStructure.
Load mOrderStructure.
Load hTerm.
Set Implicit Arguments.
Unset Strict Implicit.
Definition divTerm : Term A n -> forall (b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), Term A n.
intros H; case H; intros b2 c2 H'; case H'; intros b3 c3; simpl in |- *.
intros nZb3; exact (divA b2 b3 nZb3, div_mon n c2 c3).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve eqTerm_divTerm_comp : core.
Hint Resolve divTerm_multTerm_l divTerm_multTerm_r : core.
Hint Resolve div_is_T1 : core.
Let gb : mon n * bool -> bool.
intros H'; case H'; auto.
Defined.
Let gm : mon n * bool -> mon n.
intros H'; case H'; auto.
Defined.
Definition mk_clean : forall a b : mon n, {c : mon n * bool | c = div_mon_clean n a b}.
intros a b; exists (div_mon_clean n a b); auto.
Set Implicit Arguments.
Unset Strict Implicit.
Definition ppc : Term A n -> Term A n -> Term A n.
intros H; case H; intros b2 c2 H'; case H'; intros b3 c3; simpl in |- *; exact (A1, ppcm_mon n c2 c3).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Inductive divP : Term A n -> Term A n -> Prop := divTerm_def : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b) -> divP a b.
Hint Resolve divP_inv1 divP_inv2 divP_inv3 : core.
Hint Resolve divP_plusTerm : core.
Hint Resolve divP_invTerm_l : core.
Hint Resolve divTerm_nZ : core.
Hint Resolve divP_invTerm_r : core.
Hint Resolve divTerm_multTermr divTerm_multTerml : core.
Hint Resolve divP_trans : core.
Hint Resolve divP_nZero : core.
Hint Resolve divP_on_eqT divP_on_eqT_eqT : core.
Inductive ppcm (p q : Term A n) : Term A n -> Prop := ppcm0 : forall s : Term A n, (forall r : Term A n, divP r p -> divP r q -> divP r s) -> divP s p -> divP s q -> ppcm p q s.
Hint Resolve ppcm0 : core.
Hint Resolve ppc_multTerm_divP : core.
Hint Resolve divP_multTerm_r divP_multTerm_l : core.
Hint Resolve divP_ppcl divP_ppcr : core.
Hint Resolve divTerm_compo : core.
Hint Resolve eqT_nzero_divP : core.
Hint Resolve eqT_nzero_eqT_divP : core.
End DivTerm.

Theorem eqT_divTerm_plusTerm : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c), eqT a b -> eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZc) c) -> eqTerm (A:=A) eqA (n:=n) b (multTerm (A:=A) multA (n:=n) (divTerm b nZc) c) -> eqTerm (A:=A) eqA (n:=n) (divTerm (plusTerm (A:=A) plusA (n:=n) a b) nZc) (plusTerm (A:=A) plusA (n:=n) (divTerm a nZc) (divTerm b nZc)).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a0 m a1 m0 a2 m1 nZc H' H'0 H'1; split; auto.
case H'1; intros H'3 H'4; clear H'1.
case H'0; intros H'2 H'5; clear H'0.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := divA (plusA (multA (divA a2 a0 nZc) a0) (multA (divA a1 a0 nZc) a0)) a0 nZc); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := divA (multA (plusA (divA a2 a0 nZc) (divA a1 a0 nZc)) a0) a0 nZc); auto.
apply divA_eqA_comp with (1 := cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA (multA a0 (divA a2 a0 nZc)) (multA a0 (divA a1 a0 nZc))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA a0 (plusA (divA a2 a0 nZc) (divA a1 a0 nZc))); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA (plusA (divA a2 a0 nZc) (divA a1 a0 nZc)) (divA a0 a0 nZc)); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := divA (multA a0 (plusA (divA a2 a0 nZc) (divA a1 a0 nZc))) a0 nZc); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA (divA a0 a0 nZc) (plusA (divA a2 a0 nZc) (divA a1 a0 nZc))); auto.
apply divA_multA_comp_r with (1 := cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA (plusA (divA a2 a0 nZc) (divA a1 a0 nZc)) A1); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply multA_eqA_comp with (1 := cs); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply divA_A1 with (1 := cs); auto.
apply multA_A1_r with (1 := cs); auto.
