Require Import Bool.
Require Import NArith Ndec.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Definition prec_list_ref_ok (p : prec_list) (d : preDTA) : Prop := forall a : ad, prec_occur p a -> exists s : state, MapGet state d a = Some s.
Definition state_ref_ok (s : state) (d : preDTA) : Prop := forall (a : ad) (p : prec_list), MapGet prec_list s a = Some p -> prec_list_ref_ok p d.
Definition preDTA_ref_ok (d : preDTA) : Prop := forall (a : ad) (s : state) (c : ad) (pl : prec_list) (b : ad), MapGet state d a = Some s -> MapGet prec_list s c = Some pl -> prec_occur pl b -> exists s0 : state, MapGet state d b = Some s0.
Definition preDTA_ref_ok_distinct (d d' : preDTA) : Prop := forall (a : ad) (s : state), MapGet state d a = Some s -> state_ref_ok s d'.
Definition DTA_ref_ok (d : DTA) : Prop := match d with | dta p a => preDTA_ref_ok p end.
Definition addr_in_dta_check (d : preDTA) (a : ad) : bool := match MapGet state d a with | None => false | Some _ => true end.
Fixpoint prec_list_ref_ok_check (p : prec_list) : preDTA -> bool := fun d : preDTA => match p with | prec_empty => true | prec_cons a la ls => addr_in_dta_check d a && (prec_list_ref_ok_check la d && prec_list_ref_ok_check ls d) end.
Fixpoint state_ref_ok_check (s : state) : preDTA -> bool := fun d : preDTA => match s with | M0 => true | M1 a p => prec_list_ref_ok_check p d | M2 x y => state_ref_ok_check x d && state_ref_ok_check y d end.
Fixpoint predta_ref_ok_check_0 (d : preDTA) : preDTA -> bool := fun d' : preDTA => match d with | M0 => true | M1 a s => state_ref_ok_check s d' | M2 x y => predta_ref_ok_check_0 x d' && predta_ref_ok_check_0 y d' end.
Definition predta_ref_ok_check (d : preDTA) : bool := predta_ref_ok_check_0 d d.
Definition dta_ref_ok_check (d : DTA) : bool := match d with | dta p a => predta_ref_ok_check p end.
Definition addr_in_preDTA (d : preDTA) (a : ad) : Prop := exists s : state, MapGet state d a = Some s.
Definition DTA_main_state_correct (d : DTA) : Prop := match d with | dta p a => addr_in_preDTA p a end.
Definition DTA_main_state_correct_check (d : DTA) : bool := match d with | dta p a => match MapGet state p a with | None => false | Some _ => true end end.

Lemma predta_ref_ok_check_complete_0 : forall d d' : preDTA, predta_ref_ok_check_0 d d' = true -> preDTA_ref_ok_distinct d d'.
Proof.
unfold preDTA_ref_ok_distinct in |- *.
simple induction d; simpl in |- *; intros.
inversion H0.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H1 in H0; inversion H0.
rewrite <- H3.
exact (state_ref_ok_check_complete _ _ H).
elim (bool_is_true_or_false (predta_ref_ok_check_0 m d')); intros; rewrite H3 in H1.
elim (bool_is_true_or_false (predta_ref_ok_check_0 m0 d')); intros; rewrite H4 in H1.
induction a as [| p].
exact (H d' H3 N0 s H2).
induction p as [p Hrecp| p Hrecp| ].
exact (H0 d' H4 (Npos p) s H2).
exact (H d' H3 (Npos p) s H2).
exact (H0 d' H4 N0 s H2).
inversion H1.
inversion H1.
