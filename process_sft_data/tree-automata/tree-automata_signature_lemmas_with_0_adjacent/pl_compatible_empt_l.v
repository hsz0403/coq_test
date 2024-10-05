Require Import Bool.
Require Import NArith.
Require Import Ndec.
Require Import ZArith.
Require Import EqNat.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Definition pl_compat (pl0 pl1 : prec_list) : Prop := pl0 = prec_empty /\ pl1 = prec_empty \/ pl0 <> prec_empty /\ pl1 <> prec_empty.
Definition mpl_compat (s0 s1 : state) : Prop := forall (c : ad) (p0 p1 : prec_list), MapGet prec_list s0 c = Some p0 -> MapGet prec_list s1 c = Some p1 -> pl_compat p0 p1.
Definition dta_correct (d : preDTA) : Prop := forall (s0 s1 : state) (a0 a1 : ad), MapGet state d a0 = Some s0 -> MapGet state d a1 = Some s1 -> mpl_compat s0 s1.
Definition dta_compat (d0 d1 : preDTA) : Prop := forall (s0 s1 : state) (a0 a1 : ad), MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> mpl_compat s0 s1.
Definition DTA_compat (d0 d1 : DTA) : Prop := match d0, d1 with | dta p0 a0, dta p1 a1 => dta_compat p0 p1 end.
Inductive pl_tl_length : prec_list -> nat -> Prop := | pl_tl_O : pl_tl_length prec_empty 0 | pl_tl_S : forall (a : ad) (pl : prec_list) (n : nat), pl_tl_length pl n -> pl_tl_length (prec_cons a pl prec_empty) (S n) | pl_tl_propag : forall (a : ad) (la ls : prec_list) (n : nat), pl_tl_length la n -> pl_tl_length ls (S n) -> pl_tl_length (prec_cons a la ls) (S n).
Definition pl_tl_length_rec_def_0 (n : nat) := forall (d : preDTA) (pl : prec_list) (tl : term_list), pl_tl_length pl n -> liste_reconnait d pl tl -> n = lst_length tl.
Definition pl_tl_length_rec_def_1 (d : preDTA) (pl : prec_list) (tl : term_list) := forall n : nat, pl_tl_length_rec_def_0 n -> pl_tl_length pl (S n) -> liste_reconnait d pl tl -> S n = lst_length tl.
Definition pl_compatible (pl0 pl1 : prec_list) : Prop := exists n : nat, pl_tl_length pl0 n /\ pl_tl_length pl1 n.
Definition st_compatible (s0 s1 : state) : Prop := forall (c : ad) (pl0 pl1 : prec_list), MapGet prec_list s0 c = Some pl0 -> MapGet prec_list s1 c = Some pl1 -> pl_compatible pl0 pl1.
Definition predta_compatible (d0 d1 : preDTA) : Prop := forall s0 s1 : state, state_in_dta d0 s0 -> state_in_dta d1 s1 -> st_compatible s0 s1.
Definition dta_compatible (d0 d1 : DTA) : Prop := match d0, d1 with | dta p0 a0, dta p1 a1 => predta_compatible p0 p1 end.
Definition st_compatible_compat_def (s0 : state) : Prop := forall s1 : state, st_compatible s0 s1 -> mpl_compat s0 s1.
Definition predta_compatible_compat_def (d0 : preDTA) : Prop := forall d1 : preDTA, predta_compatible d0 d1 -> dta_compat d0 d1.
Definition signature : Set := Map nat.
Definition state_correct_wrt_sign (s : state) (sigma : signature) : Prop := forall (a : ad) (p : prec_list), MapGet prec_list s a = Some p -> exists n : nat, MapGet nat sigma a = Some n /\ pl_tl_length p n.
Definition predta_correct_wrt_sign (d : preDTA) (sigma : signature) : Prop := forall (a : ad) (s : state), MapGet state d a = Some s -> state_correct_wrt_sign s sigma.
Definition dta_correct_wrt_sign (d : DTA) (sigma : signature) : Prop := match d with | dta d a => predta_correct_wrt_sign d sigma end.
Fixpoint pl_compat_check (p : prec_list) : option nat := match p with | prec_empty => Some 0 | prec_cons a la ls => match ls with | prec_empty => match pl_compat_check la with | None => None | Some n => Some (S n) end | prec_cons _ _ _ => match pl_compat_check la, pl_compat_check ls with | None, _ => None | _, None => None | Some n, Some m => if beq_nat (S n) m then Some m else None end end end.
Inductive pre_ad : Set := | pre_ad_empty : pre_ad | pre_ad_O : pre_ad -> pre_ad | pre_ad_I : pre_ad -> pre_ad.
Fixpoint pre_ad_concat (pa : pre_ad) : ad -> ad := fun a : ad => match pa with | pre_ad_empty => a | pre_ad_O pa' => pre_ad_concat pa' (N.double a) | pre_ad_I pa' => pre_ad_concat pa' (Ndouble_plus_one a) end.
Fixpoint st_compat_check_0 (pa : pre_ad) (sigma : signature) (s : state) {struct s} : bool := match s with | M0 => true | M1 a p => match pl_compat_check p, MapGet nat sigma (pre_ad_concat pa a) with | None, _ => false | _, None => false | Some n, Some m => beq_nat n m end | M2 x y => st_compat_check_0 (pre_ad_O pa) sigma x && st_compat_check_0 (pre_ad_I pa) sigma y end.
Definition st_compat_check (s : state) (sigma : signature) : bool := st_compat_check_0 pre_ad_empty sigma s.
Fixpoint predta_compat_check (d : preDTA) : signature -> bool := fun sigma : signature => match d with | M0 => true | M1 a s => st_compat_check s sigma | M2 x y => predta_compat_check x sigma && predta_compat_check y sigma end.
Definition dta_compat_check (d : DTA) (sigma : signature) : bool := match d with | dta p a => predta_compat_check p sigma end.
Definition state_correct_wrt_sign_with_offset (s : state) (sigma : signature) (pa : pre_ad) : Prop := forall (a : ad) (p : prec_list), MapGet prec_list s a = Some p -> exists n : nat, MapGet nat sigma (pre_ad_concat pa a) = Some n /\ pl_tl_length p n.

Lemma pl_compatible_empt_l : forall p : prec_list, pl_compatible prec_empty p -> p = prec_empty.
Proof.
intros.
exact (pl_compatible_empt_r p (pl_compatible_sym prec_empty p H)).
