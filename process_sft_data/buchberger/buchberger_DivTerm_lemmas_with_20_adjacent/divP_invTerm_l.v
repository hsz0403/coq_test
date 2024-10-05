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

Theorem zeroP_divTerm : forall a b : Term A n, zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, zeroP (A:=A) A0 eqA (n:=n) (divTerm a nZb).
intros a b; case a; case b; simpl in |- *; auto.
intros d H' A0' H'0 H'1 nZd; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := divA A0 d nZd); auto.
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

Theorem divP_inv1 : forall a b : Term A n, divP a b -> ~ zeroP (A:=A) A0 eqA (n:=n) a.
Admitted.

Theorem divP_inv2 : forall a b : Term A n, divP a b -> ~ zeroP (A:=A) A0 eqA (n:=n) b.
Admitted.

Theorem divP_inv3 : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), divP a b -> eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b).
intros a b nZb H; inversion H; auto.
Admitted.

Theorem divP_plusTerm : forall a b c : Term A n, divP a c -> divP b c -> eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) -> divP (plusTerm (A:=A) plusA (n:=n) a b) c.
intros a b c H' H'0; inversion H'0; inversion H'.
intros H'1 H'2; apply divTerm_def with (nZb := nZb0); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := plusTerm (A:=A) plusA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm a nZb0) c) (multTerm (A:=A) multA (n:=n) (divTerm b nZb0) c)); auto.
apply eqTerm_plusTerm_comp with (1 := cs); auto.
apply multTerm_eqT; auto.
apply eqT_divTerm; auto.
apply (eqT_refl A n).
apply (eqT_refl A n).
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (plusTerm (A:=A) plusA (n:=n) (divTerm a nZb0) (divTerm b nZb0)) c); auto.
apply multTerm_plusTerm_dist_l with (1 := cs); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Admitted.

Theorem divP_invTerm_r : forall a b : Term A n, divP a b -> divP a (invTerm (A:=A) invA (n:=n) b).
intros a b H'; inversion H'.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (invTerm (A:=A) invA (n:=n) b)); [ intros nZib | auto ].
apply divTerm_def with (nZb := nZib); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (divTerm a nZb)) (invTerm (A:=A) invA (n:=n) b)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm a nZb) (invTerm (A:=A) invA (n:=n) b))); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b))); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm a nZb) b); auto.
apply eqTerm_invTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply mult_invTerm_com_r with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply mult_invTerm_com with (1 := cs); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
Admitted.

Theorem divTerm_multTerml : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> divP (multTerm (A:=A) multA (n:=n) a b) a.
intros a b nZa nZb.
apply divTerm_def with (nZb := nZa); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm a nZa) b) a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) b) a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) b a); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply div_is_T1; auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
Admitted.

Theorem divTerm_multTermr : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> divP (multTerm (A:=A) multA (n:=n) a b) b.
intros a b nZa nZb.
apply divTerm_def with (nZb := nZb); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (divTerm b nZb)) b); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
Admitted.

Theorem divP_trans : transitive (Term A n) divP.
red in |- *; intros a b c H' H'0.
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros nZc | auto ].
apply divTerm_def with (nZb := nZc); auto.
apply divP_inv1 with (b := b); auto.
2: apply divP_inv2 with (a := b); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZb | auto ].
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm a nZb) (divTerm b nZc)) c); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm a nZb) (multTerm (A:=A) multA (n:=n) (divTerm b nZc) c)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm a nZb) b); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
inversion H'0; inversion H'.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b) nZc); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_multTerm_l; auto.
apply eqTerm_divTerm_comp; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (1 := H4); auto.
Admitted.

Theorem divP_nZero : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), divP a b -> ~ zeroP (A:=A) A0 eqA (n:=n) (divTerm a nZb).
Admitted.

Theorem divP_eqTerm_comp : forall a b c : Term A n, divP a c -> eqTerm (A:=A) eqA (n:=n) a b -> divP b c.
intros a b c H' H'0.
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros nZc | auto ].
apply divTerm_def with (nZb := nZc); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := a); auto.
apply divP_inv1 with (b := c); auto.
2: apply divP_inv2 with (a := a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm a nZc) c); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := a); auto.
Admitted.

Theorem divP_on_eqT : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> eqT a b -> divP a b.
intros a b H' nZb H'1; apply divTerm_def with (nZb := nZb); auto.
Admitted.

Theorem divP_on_eqT_eqT : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> forall nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b, eqT a b -> eqT (divTerm a nZb) (T1 A1 n).
Admitted.

Theorem ppc_is_ppcm : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> ppcm a b (ppc a b).
intros a b nZa nZb; apply ppcm0; auto.
intros r H'1 H'2; inversion H'1; inversion H'2.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc a b)); [ intros nZppab | auto ].
apply divTerm_def with (nZb := nZppab); auto.
apply divTerm_ppc with (nZa := nZa) (nZb := nZb); auto.
apply ppc_nZ; auto.
apply divTerm_def with (nZb := nZa); auto.
apply ppc_nZ; auto.
apply divTerm_ppcl; auto.
apply divTerm_def with (nZb := nZb); auto.
apply ppc_nZ; auto.
Admitted.

Theorem ppc_multTerm_divP : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> divP (multTerm (A:=A) multA (n:=n) a b) (ppc a b).
intros a b H' H'0.
Admitted.

Theorem divP_comp : forall a b c d : Term A n, divP a c -> eqTerm (A:=A) eqA (n:=n) a b -> eqTerm (A:=A) eqA (n:=n) c d -> divP b d.
intros a b c d H'; generalize b d; elim H'.
intros a0 b0 nZa0 nZb0 H'2 b1 d0 H'3 H'4; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) d0); [ intros nZd0 | auto ].
apply divTerm_def with (nZb := nZd0); auto.
red in |- *; intros nz1; absurd (zeroP (A:=A) A0 eqA (n:=n) a0); auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := b1); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := a0); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm a0 nZb0) b0); auto.
red in |- *; intros nz1; absurd (zeroP (A:=A) A0 eqA (n:=n) b0); auto.
apply zeroP_comp_eqTerm with (1 := cs) (a := d0); auto.
Admitted.

Theorem divP_multTerm_l : forall a b c : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> eqTerm (A:=A) eqA (n:=n) (multTerm (A:=A) multA (n:=n) a b) c -> divP c a.
intros a b c H' H'0 H'1.
Admitted.

Theorem divP_multTerm_r : forall a b c : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> eqTerm (A:=A) eqA (n:=n) (multTerm (A:=A) multA (n:=n) a b) c -> divP c b.
intros a b c H' H'0 H'1.
Admitted.

Theorem divP_ppcl : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> divP (ppc a b) a.
intros a b H' H'0; try assumption.
lapply (ppc_is_ppcm a b); [ intros H'3; lapply H'3; clear H'3; [ intros H'4 | idtac ] | idtac ]; auto; auto.
Admitted.

Theorem divP_ppcr : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> divP (ppc a b) b.
intros a b H' H'0; try assumption.
lapply (ppc_is_ppcm a b); [ intros H'3; lapply H'3; clear H'3; [ intros H'4 | idtac ] | idtac ]; auto; auto.
Admitted.

Theorem divTerm_compo : forall (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c), divP a b -> divP b c -> eqTerm (A:=A) eqA (n:=n) (divTerm a nZc) (multTerm (A:=A) multA (n:=n) (divTerm a nZb) (divTerm b nZc)).
intros a b c nZb nZc H'; inversion H'.
intros H'0; inversion H'0.
Admitted.

Theorem divP_comp_ppc0 : forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZppab : ~ zeroP (A:=A) A0 eqA (n:=n) (ppc a b)) (p : list (Term A n)), eqTerm (A:=A) eqA (n:=n) b (multTerm (A:=A) multA (n:=n) (divTerm (multTerm (A:=A) multA (n:=n) a b) nZppab) (divTerm (ppc a b) nZa)).
intros a b nZa nZb nZppab p.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm a nZa) b); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) a b) nZa); auto.
Admitted.

Theorem divP_comp_ppc1 : forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (nZppab : ~ zeroP (A:=A) A0 eqA (n:=n) (ppc a b)) (p : list (Term A n)), eqTerm (A:=A) eqA (n:=n) a (multTerm (A:=A) multA (n:=n) (divTerm (multTerm (A:=A) multA (n:=n) a b) nZppab) (divTerm (ppc a b) nZb)).
intros a b nZa nZb nZppab H'0.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) a (divTerm b nZb)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) a b) nZb); auto.
Admitted.

Theorem divP_dec : forall a b : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> {divP a b} + {~ divP a b}.
intros a b nZa nZb.
elim divTerm_dec with (a := a) (nZb := nZb); auto.
Admitted.

Theorem divP_eqT : forall a b c : Term A n, eqT a b -> ~ zeroP (A:=A) A0 eqA (n:=n) b -> divP a c -> divP b c.
intros a b c H' nZb H'1; inversion H'1.
apply divTerm_def with (nZb := nZb0); auto.
Admitted.

Theorem divP_invTerm_l : forall a b : Term A n, divP a b -> divP (invTerm (A:=A) invA (n:=n) a) b.
intros a b H'; inversion H'; auto.
apply divTerm_def with (nZb := nZb); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (divTerm a nZb)) b); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply mult_invTerm_com with (1 := cs); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_invTerm_l; auto.
