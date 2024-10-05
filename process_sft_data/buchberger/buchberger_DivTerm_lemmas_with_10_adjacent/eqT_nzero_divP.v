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

Theorem eqTerm_multTerm_imp_eqTerm : forall a b c : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) c -> eqTerm (A:=A) eqA (n:=n) (multTerm (A:=A) multA (n:=n) c a) (multTerm (A:=A) multA (n:=n) c b) -> eqTerm (A:=A) eqA (n:=n) a b.
intros a b c nZc H'0.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) c a) nZc); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm c nZc) a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm c nZc) a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) c b) nZc); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (divTerm c nZc) b); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) b); auto.
Admitted.

Theorem multTerm_eqTerm_inv : forall a b c : Term A n, eqTerm (A:=A) eqA (n:=n) (multTerm (A:=A) multA (n:=n) a b) (multTerm (A:=A) multA (n:=n) a c) -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqTerm (A:=A) eqA (n:=n) b c.
intros a b c H' H'1.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) b (divTerm a H'1)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) b a) H'1); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) a b) H'1); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) c (divTerm a H'1)); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) c a) H'1); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := divTerm (multTerm (A:=A) multA (n:=n) a c) H'1); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := multTerm (A:=A) multA (n:=n) c (T1 A1 n)); auto.
Admitted.

Theorem eqT_nzero_eqT_divP : forall (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), eqT c (multTerm (A:=A) multA (n:=n) (divTerm c nZb) b) -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqT a c -> divP a b.
intros a b c nZb H'0 H'1 H'2.
apply eqT_nzero_divP with (nZb := nZb); auto.
apply (eqT_trans A n) with (y := c); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (divTerm c nZb) b); auto.
apply (eqT_sym A n); auto.
apply multTerm_eqT; auto.
apply eqT_divTerm; auto; apply (eqT_refl A n); auto.
Admitted.

Theorem eqT_nzero_divP : forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), eqT a (multTerm (A:=A) multA (n:=n) (divTerm a nZb) b) -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> divP a b.
intros a b nZb H'0 H'1; auto.
apply divP_eqT with (a := multTerm (A:=A) multA (n:=n) (divTerm a nZb) b); auto.
apply (eqT_sym A n); auto.
