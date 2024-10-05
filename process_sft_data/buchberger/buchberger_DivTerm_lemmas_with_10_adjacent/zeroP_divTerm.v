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

Theorem eqTerm_divTerm_comp : forall (a b c d : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (nZd : ~ zeroP (A:=A) A0 eqA (n:=n) d), eqTerm (A:=A) eqA (n:=n) a b -> eqTerm (A:=A) eqA (n:=n) c d -> eqTerm (A:=A) eqA (n:=n) (divTerm a nZc) (divTerm b nZd).
intros a b c d; case a; case b; case c; case d; simpl in |- *; auto.
intros A0' c0 d2 c2 d3 c3 d4 c4 nZd2 H'0 H'1 H'2.
case H'2; intros H'3 H'4; clear H'2.
case H'1; intros H'2 H'5; clear H'1.
split; auto.
Admitted.

Theorem divTerm_multTerm_l : forall (a b c : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), eqTerm (A:=A) eqA (n:=n) b (multTerm (A:=A) multA (n:=n) (divTerm b nZa) a) -> eqTerm (A:=A) eqA (n:=n) (divTerm (multTerm (A:=A) multA (n:=n) c b) nZa) (multTerm (A:=A) multA (n:=n) c (divTerm b nZa)).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros d c0 A0' c2 d2 c3 nZd2 H'0; case H'0; intros H'1 H'2; auto.
split; auto.
apply divA_multA_comp_l with (1 := cs).
rewrite H'2.
repeat rewrite mult_div_com.
rewrite mult_mon_assoc.
Admitted.

Theorem divTerm_multTerm_r : forall (a b c : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), eqTerm (A:=A) eqA (n:=n) b (multTerm (A:=A) multA (n:=n) (divTerm b nZa) a) -> eqTerm (A:=A) eqA (n:=n) (divTerm (multTerm (A:=A) multA (n:=n) b c) nZa) (multTerm (A:=A) multA (n:=n) (divTerm b nZa) c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a0 m a1 m0 a2 m1 nZa H'; split; auto.
apply divA_multA_comp_r with (1 := cs).
elim H'; intros H'0 H'1; rewrite H'1; clear H'.
rewrite mult_div_com; auto.
rewrite <- mult_mon_assoc.
rewrite (mult_mon_com n m1 m).
rewrite mult_mon_assoc.
Admitted.

Theorem div_is_T1 : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), eqTerm (A:=A) eqA (n:=n) (divTerm a nZa) (T1 A1 n).
intros a; case a; simpl in |- *; auto.
intros a0 m nZa; split; auto.
apply divA_A1 with (1 := cs).
Admitted.

Theorem divTerm_nZ : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, ~ zeroP (A:=A) A0 eqA (n:=n) (divTerm a nZb).
intros a b; case a; case b; simpl in |- *; auto.
Admitted.

Theorem divTerm_eqT : forall a b c : Term A n, eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> forall nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c, eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZc) c) -> eqTerm (A:=A) eqA (n:=n) b (multTerm (A:=A) multA (n:=n) (divTerm b nZc) c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a1 m1 a2 m2 a3 m3 H1 H2 H3 H4 H5; case H5; intros H6 H7; split; auto.
apply divA_is_multA with (1 := cs); auto.
Admitted.

Let gb : mon n * bool -> bool.
Admitted.

Let gm : mon n * bool -> mon n.
Admitted.

Definition mk_clean : forall a b : mon n, {c : mon n * bool | c = div_mon_clean n a b}.
Admitted.

Theorem divTerm_dec : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, {eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b)} + {~ eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b)}.
intros a b; case a; case b; simpl in |- *; auto.
intros b2 c2 b3 c3.
intros Zp1 Zp2.
case (mk_clean c3 c2).
intros x; case x.
intros c b4; case b4.
intros H0; left; simpl in |- *; auto.
generalize (div_clean_dec1 n c3 c2); rewrite <- H0; simpl in |- *; auto.
intros H1; case H1; auto; intros H2 H3; split; auto.
apply divA_is_multA with (1 := cs); auto.
intros H0; right; red in |- *; intros dviP_H; inversion dviP_H.
generalize (div_clean_dec2 n c3 c2); simpl in |- *; auto.
intros H'; lapply H'; [ intros H'0; apply H'0; clear H' | clear H' ].
rewrite <- H1; auto.
Admitted.

Theorem divTerm_on_eqT : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, eqT a b -> eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b).
intros a b; case a; case b; unfold eqT in |- *; simpl in |- *; auto.
intros d c A0' c0 H' H'0 H'1; rewrite <- H'1.
split; auto.
apply divA_is_multA with (1 := cs); auto.
rewrite mult_div_id; auto.
Admitted.

Theorem divTerm_on_eqT_eqT : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, eqT a b -> eqT (divTerm a nZb) (T1 A1 n).
intros a b; case a; case b; unfold eqT in |- *; simpl in |- *; auto.
intros b2 c b3 c0 H' H'0 H'1; rewrite H'1; auto.
Admitted.

Theorem divTerm_on_plusM_minusM : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, T2M a = mult_mon n (div_mon n (T2M a) (T2M b)) (T2M b) -> eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b).
intros a b; case a; case b; simpl in |- *; auto.
split; auto.
Admitted.

Definition ppc : Term A n -> Term A n -> Term A n.
Admitted.

Theorem ppc_com : forall a b : Term A n, eqTerm (A:=A) eqA (n:=n) (ppc a b) (ppc b a).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0; split; auto.
Admitted.

Theorem divTerm_ppc : forall (a b c : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZppab : ~ zeroP (A:=A) A0 eqA (n:=n) (ppc a b)), eqTerm (A:=A) eqA (n:=n) c (multTerm (A:=A) multA (n:=n) (divTerm c nZa) a) -> eqTerm (A:=A) eqA (n:=n) c (multTerm (A:=A) multA (n:=n) (divTerm c nZb) b) -> eqTerm (A:=A) eqA (n:=n) c (multTerm (A:=A) multA (n:=n) (divTerm c nZppab) (ppc a b)).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a0 m a1 m0 a2 m1 nZa nZb nZppab H H0; split; auto.
apply divA_is_multA with (1 := cs); auto.
Admitted.

Theorem divTerm_ppcl : forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), ~ zeroP (A:=A) A0 eqA (n:=n) b -> eqTerm (A:=A) eqA (n:=n) (ppc a b) (multTerm (A:=A) multA (n:=n) (divTerm (ppc a b) nZa) a).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 nZa H; split; auto.
apply divA_is_multA with (1 := cs); auto.
Admitted.

Theorem divTerm_ppcr : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, eqTerm (A:=A) eqA (n:=n) (ppc a b) (multTerm (A:=A) multA (n:=n) (divTerm (ppc a b) nZb) b).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 H nZb; split; auto.
apply divA_is_multA with (1 := cs); auto.
Admitted.

Theorem ppc_nZ : forall a b c : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> ~ zeroP (A:=A) A0 eqA (n:=n) (ppc a b).
Admitted.

Theorem divTerm_rew : forall (a b : Term A n) (nZ1 nZ2 : ~ zeroP (A:=A) A0 eqA (n:=n) b), divTerm a nZ1 = divTerm a nZ2.
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 nZ1 nZ2.
Admitted.

Theorem zeroP_divTerm : forall a b : Term A n, zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, zeroP (A:=A) A0 eqA (n:=n) (divTerm a nZb).
intros a b; case a; case b; simpl in |- *; auto.
intros d H' A0' H'0 H'1 nZd; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := divA A0 d nZd); auto.
apply divA_A0_l with (1 := cs).
