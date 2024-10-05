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

Lemma pl_compat_sym : forall pl0 pl1 : prec_list, pl_compat pl0 pl1 -> pl_compat pl1 pl0.
Proof.
unfold pl_compat in |- *.
intros.
elim H; intros.
elim H0.
intros.
left.
split; assumption.
elim H0.
intros.
right.
Admitted.

Lemma mpl_compat_0 : forall (c : ad) (pl0 pl1 : prec_list), mpl_compat (M1 prec_list c pl0) (M1 prec_list c pl1) -> pl_compat pl0 pl1.
Proof.
intros.
unfold mpl_compat in H.
apply (H c pl0 pl1).
simpl in |- *.
rewrite (Neqb_correct c).
trivial.
simpl in |- *.
rewrite (Neqb_correct c).
Admitted.

Lemma mpl_compat_1 : forall s0 s1 s2 s3 : state, mpl_compat (M2 prec_list s0 s1) (M2 prec_list s2 s3) -> mpl_compat s0 s2.
Proof.
intros.
unfold mpl_compat in H.
unfold mpl_compat in |- *.
intros.
induction c as [| p].
apply (H N0 p0 p1).
simpl in |- *.
assumption.
simpl in |- *.
assumption.
apply (H (Npos (xO p)) p0 p1).
simpl in |- *.
assumption.
simpl in |- *.
Admitted.

Lemma mpl_compat_2 : forall s0 s1 s2 s3 : state, mpl_compat (M2 prec_list s0 s1) (M2 prec_list s2 s3) -> mpl_compat s1 s3.
Proof.
intros.
unfold mpl_compat in H.
unfold mpl_compat in |- *.
intros.
induction c as [| p].
apply (H (Npos 1) p0 p1).
simpl in |- *.
assumption.
simpl in |- *.
assumption.
apply (H (Npos (xI p)) p0 p1).
simpl in |- *.
assumption.
simpl in |- *.
Admitted.

Lemma mpl_compat_4 : forall (s0 s1 : state) (pl : prec_list), mpl_compat (M2 prec_list s0 s1) (M1 prec_list (Npos 1) pl) -> mpl_compat s1 (M1 prec_list N0 pl).
Proof.
intros.
unfold mpl_compat in |- *.
unfold mpl_compat in H.
intros.
unfold MapGet in H1.
elim (bool_is_true_or_false (N.eqb N0 c)); intros; rewrite H2 in H1; inversion H1.
rewrite H4 in H.
apply (H (Npos 1) p0 p1).
simpl in |- *.
rewrite <- (Neqb_complete N0 c H2) in H0.
assumption.
simpl in |- *.
Admitted.

Lemma mpl_compat_5 : forall (s0 s1 : state) (pl : prec_list) (p : positive), mpl_compat (M2 prec_list s0 s1) (M1 prec_list (Npos (xO p)) pl) -> mpl_compat s0 (M1 prec_list (Npos p) pl).
Proof.
unfold mpl_compat in |- *.
intros.
unfold MapGet in H1.
elim (bool_is_true_or_false (N.eqb (Npos p) c)); intros; rewrite H2 in H1; inversion H1.
rewrite H4 in H.
apply (H (Npos (xO p)) p0 p1).
simpl in |- *.
rewrite <- (Neqb_complete (Npos p) c H2) in H0.
assumption.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
Admitted.

Lemma mpl_compat_6 : forall (s0 s1 : state) (pl : prec_list) (p : positive), mpl_compat (M2 prec_list s0 s1) (M1 prec_list (Npos (xI p)) pl) -> mpl_compat s1 (M1 prec_list (Npos p) pl).
Proof.
unfold mpl_compat in |- *.
intros.
unfold MapGet in H1.
elim (bool_is_true_or_false (N.eqb (Npos p) c)); intros; rewrite H2 in H1; inversion H1.
rewrite H4 in H.
apply (H (Npos (xI p)) p0 p1).
simpl in |- *.
rewrite <- (Neqb_complete (Npos p) c H2) in H0.
assumption.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
Admitted.

Lemma mpl_compat_sym : forall s0 s1 : state, mpl_compat s0 s1 -> mpl_compat s1 s0.
Proof.
unfold mpl_compat in |- *.
intros.
apply (pl_compat_sym p1 p0).
Admitted.

Lemma pl_tl_length_pl_compat : forall (p0 p1 : prec_list) (n : nat), pl_tl_length p0 n -> pl_tl_length p1 n -> pl_compat p0 p1.
Proof.
intros.
inversion H.
inversion H0.
unfold pl_compat in |- *.
left.
split; reflexivity.
rewrite <- H2 in H5.
inversion H5.
rewrite <- H2 in H6.
inversion H6.
inversion H0.
rewrite <- H5 in H3.
inversion H3.
unfold pl_compat in |- *.
right.
split; intro; inversion H7.
unfold pl_compat in |- *.
right.
split; intro; inversion H8.
inversion H0.
rewrite <- H6 in H4.
inversion H4.
unfold pl_compat in |- *.
right.
split; intro; inversion H8.
unfold pl_compat in |- *.
right.
Admitted.

Lemma pl_tl_length_rec_0 : pl_tl_length_rec_def_0 0.
Proof.
unfold pl_tl_length_rec_def_0 in |- *.
intros.
inversion H.
rewrite <- H1 in H0.
inversion H0.
Admitted.

Lemma pl_tl_length_rec_1 : forall d : preDTA, pl_tl_length_rec_def_1 d prec_empty tnil.
Proof.
unfold pl_tl_length_rec_def_1 in |- *.
intros.
Admitted.

Lemma pl_tl_length_rec_2 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list), reconnaissance d a hd -> liste_reconnait d la tl -> pl_tl_length_rec_def_1 d la tl -> pl_tl_length_rec_def_1 d (prec_cons a la ls) (tcons hd tl).
Proof.
unfold pl_tl_length_rec_def_1 in |- *.
intros.
simpl in |- *.
unfold pl_tl_length_rec_def_0 in H2.
rewrite (H2 d la tl).
reflexivity.
inversion H3.
exact H6.
exact H7.
Admitted.

Lemma pl_tl_length_rec_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list), liste_reconnait d ls (tcons hd tl) -> pl_tl_length_rec_def_1 d ls (tcons hd tl) -> pl_tl_length_rec_def_1 d (prec_cons a la ls) (tcons hd tl).
Proof.
unfold pl_tl_length_rec_def_1 in |- *.
intros.
apply (H0 n H1).
inversion H2.
rewrite <- H7 in H.
inversion H.
exact H9.
Admitted.

Lemma pl_tl_length_rec_4 : forall (p : preDTA) (p0 : prec_list) (t : term_list), liste_reconnait p p0 t -> pl_tl_length_rec_def_1 p p0 t.
Proof.
Admitted.

Lemma mpl_compat_3 : forall (s0 s1 : state) (pl : prec_list), mpl_compat (M2 prec_list s0 s1) (M1 prec_list N0 pl) -> mpl_compat s0 (M1 prec_list N0 pl).
Proof.
intros.
unfold mpl_compat in H.
unfold mpl_compat in |- *.
intros.
unfold MapGet in H1.
elim (bool_is_true_or_false (N.eqb N0 c)); intros.
rewrite H2 in H1.
inversion H1.
apply (H N0 p0 p1).
simpl in |- *.
rewrite <- (Neqb_complete N0 c H2) in H0.
assumption.
simpl in |- *.
rewrite H4.
trivial.
rewrite H2 in H1.
inversion H1.
