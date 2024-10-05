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

Theorem divTerm_eqT : forall a b c : Term A n, eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> forall nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c, eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZc) c) -> eqTerm (A:=A) eqA (n:=n) b (multTerm (A:=A) multA (n:=n) (divTerm b nZc) c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a1 m1 a2 m2 a3 m3 H1 H2 H3 H4 H5; case H5; intros H6 H7; split; auto.
apply divA_is_multA with (1 := cs); auto.
unfold eqT in H1; simpl in H1; rewrite <- H1; auto.
