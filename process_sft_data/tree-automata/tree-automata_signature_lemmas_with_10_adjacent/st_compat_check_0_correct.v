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

Lemma predta_compatible_compat_2 : forall m : Map state, predta_compatible_compat_def m -> forall m0 : Map state, predta_compatible_compat_def m0 -> predta_compatible_compat_def (M2 state m m0).
Proof.
unfold predta_compatible_compat_def in |- *.
unfold dta_compat in |- *.
unfold predta_compatible in |- *.
intros.
cut (predta_compatible m d1).
cut (predta_compatible m0 d1).
unfold predta_compatible in |- *.
intros.
induction a0 as [| p].
apply (H d1) with (s0 := s0) (s1 := s1) (a0 := N0) (a1 := a1).
intros.
exact (H5 _ _ H6 H7).
simpl in H2.
assumption.
exact H3.
induction p as [p Hrecp| p Hrecp| ].
apply (H0 d1) with (s0 := s0) (s1 := s1) (a0 := Npos p) (a1 := a1).
intros.
exact (H4 _ _ H6 H7).
simpl in H2.
exact H2.
exact H3.
apply (H d1) with (s0 := s0) (s1 := s1) (a0 := Npos p) (a1 := a1).
intros.
exact (H5 _ _ H6 H7).
simpl in H2.
exact H2.
exact H3.
apply (H0 d1) with (s0 := s0) (s1 := s1) (a0 := N0) (a1 := a1).
exact H4.
simpl in H2.
exact H2.
exact H3.
unfold predta_compatible in |- *.
intros.
apply (H1 s2 s3).
elim H4.
intros.
split with (Ndouble_plus_one x).
induction x as [| p]; simpl in |- *; exact H6.
exact H5.
unfold predta_compatible in |- *.
intros.
apply (H1 s2 s3).
elim H4.
intros.
split with (N.double x); intros.
induction x as [| p]; simpl in |- *; exact H6.
Admitted.

Lemma predta_compatible_compat : forall d0 d1 : preDTA, predta_compatible d0 d1 -> dta_compat d0 d1.
Proof.
Admitted.

Lemma dta_compatible_compat : forall d0 d1 : DTA, dta_compatible d0 d1 -> DTA_compat d0 d1.
Proof.
simple induction d0.
simple induction d1.
simpl in |- *.
Admitted.

Lemma states_correct_wrt_sign_compatibles : forall (sigma : signature) (s s' : state), state_correct_wrt_sign s sigma -> state_correct_wrt_sign s' sigma -> st_compatible s s'.
Proof.
unfold st_compatible in |- *.
intros.
unfold state_correct_wrt_sign in H.
unfold state_correct_wrt_sign in H0.
elim (H _ _ H1).
elim (H0 _ _ H2).
intros.
elim H3.
elim H4.
intros.
rewrite H7 in H5.
inversion H5.
unfold pl_compatible in |- *.
split with x.
split.
rewrite H10.
exact H6.
Admitted.

Lemma predtas_correct_wrt_sign_compatibles : forall (sigma : signature) (d d' : preDTA), predta_correct_wrt_sign d sigma -> predta_correct_wrt_sign d' sigma -> predta_compatible d d'.
Proof.
unfold predta_compatible in |- *.
unfold predta_correct_wrt_sign in |- *.
intros.
elim H1.
elim H2.
intros.
Admitted.

Lemma dtas_correct_wrt_sign_compatibles : forall (sigma : signature) (d d' : DTA), dta_correct_wrt_sign d sigma -> dta_correct_wrt_sign d' sigma -> dta_compatible d d'.
Proof.
unfold dta_correct_wrt_sign in |- *.
unfold dta_compatible in |- *.
intros.
induction d as (p, a).
induction d' as (p0, a0).
Admitted.

Lemma pl_compat_check_correct : forall (p : prec_list) (n : nat), pl_tl_length p n -> pl_compat_check p = Some n.
Proof.
simple induction p.
intros.
inversion H1.
simpl in |- *.
rewrite (H _ H6).
reflexivity.
simpl in |- *.
elim (pl_sum p1); intros.
rewrite H8 in H7.
inversion H7.
elim H8.
intros.
elim H9.
intros.
elim H10.
intros.
rewrite H11.
rewrite <- H11.
rewrite (H _ H6).
rewrite (H0 _ H7).
rewrite (beq_nat_correct n0).
reflexivity.
intros.
inversion H.
Admitted.

Lemma pl_compat_check_complete : forall (p : prec_list) (n : nat), pl_compat_check p = Some n -> pl_tl_length p n.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1).
intros.
rewrite H2 in H1.
elim (option_sum nat (pl_compat_check p0)).
intro y.
elim y.
intros x y0.
rewrite y0 in H1.
inversion H1.
rewrite H2.
exact (pl_tl_S a p0 x (H _ y0)).
intro y.
rewrite y in H1.
inversion H1.
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
rewrite <- H5 in H1.
elim (option_sum nat (pl_compat_check p0)).
intro y.
elim y.
intros x2 y0.
rewrite y0 in H1.
elim (option_sum nat (pl_compat_check p1)).
intro y1.
elim y1.
intros x3 y2.
rewrite y2 in H1.
elim (nat_sum x3).
intros.
rewrite H6 in H1.
inversion H1.
intros.
elim H6.
intros.
rewrite H7 in H1.
elim (bool_is_true_or_false (beq_nat x2 x4)); intro H8; rewrite H8 in H1.
inversion H1.
rewrite (beq_nat_complete _ _ H8) in y0.
rewrite H7 in y2.
exact (pl_tl_propag _ _ _ _ (H _ y0) (H0 _ y2)).
inversion H1.
intro y1.
rewrite y1 in H1.
inversion H1.
intro y.
rewrite y in H1.
elim (option_sum nat (pl_compat_check p1)).
intros y0.
elim y0.
intros x2 y1.
inversion H1.
inversion H1.
intros.
simpl in H.
inversion H.
Admitted.

Lemma state_correct_wrt_sign_with_offset_M2 : forall (s0 s1 : state) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset (M2 prec_list s0 s1) sigma pa -> state_correct_wrt_sign_with_offset s0 sigma (pre_ad_O pa) /\ state_correct_wrt_sign_with_offset s1 sigma (pre_ad_I pa).
Proof.
unfold state_correct_wrt_sign_with_offset in |- *.
intros.
split.
intros.
elim (H (N.double a) p).
intros.
split with x.
induction a as [| p0]; simpl in |- *; simpl in H1; exact H1.
induction a as [| p0]; simpl in |- *; exact H0.
intros.
elim (H (Ndouble_plus_one a) p).
intros.
split with x.
induction a as [| p0]; simpl in |- *; simpl in H1; exact H1.
Admitted.

Lemma predta_correct_wrt_sign_M2 : forall (d0 d1 : preDTA) (sigma : signature), predta_correct_wrt_sign (M2 state d0 d1) sigma -> predta_correct_wrt_sign d0 sigma /\ predta_correct_wrt_sign d1 sigma.
Proof.
unfold predta_correct_wrt_sign in |- *.
intros.
split.
intros.
apply (H (N.double a) s).
induction a as [| p]; simpl in |- *; exact H0.
intros.
apply (H (Ndouble_plus_one a) s).
Admitted.

Lemma st_compat_check_0_complete : forall (s : state) (sigma : signature) (pa : pre_ad), st_compat_check_0 pa sigma s = true -> state_correct_wrt_sign_with_offset s sigma pa.
Proof.
unfold state_correct_wrt_sign_with_offset in |- *.
simple induction s.
intros.
inversion H0.
intros.
simpl in H.
elim (option_sum nat (pl_compat_check a0)); intro y.
elim y.
intros x y0.
rewrite y0 in H.
elim (option_sum nat (MapGet nat sigma (pre_ad_concat pa a))); intro y1.
elim y1.
intros x0 y2.
rewrite y2 in H.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a1)); intro; rewrite H1 in H0.
inversion H0.
split with x.
rewrite (beq_nat_complete _ _ H).
split.
rewrite (Neqb_complete _ _ H1) in y2.
exact y2.
rewrite (beq_nat_complete _ _ H) in y0.
rewrite H3 in y0.
exact (pl_compat_check_complete p x0 y0).
inversion H0.
rewrite y1 in H.
inversion H.
rewrite y in H.
elim (option_sum nat (MapGet nat sigma (pre_ad_concat pa a))); intro y0.
elim y0.
intros x y1.
inversion H.
inversion H.
intros.
simpl in H1.
elim (bool_is_true_or_false (st_compat_check_0 (pre_ad_O pa) sigma m)); intro; rewrite H3 in H1.
elim (bool_is_true_or_false (st_compat_check_0 (pre_ad_I pa) sigma m0)); intros; rewrite H4 in H1.
induction a as [| p0].
simpl in H2.
elim (H sigma (pre_ad_O pa) H3 N0 p H2).
intros.
split with x.
simpl in H5.
exact H5.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H2.
elim (H0 sigma (pre_ad_I pa) H4 (Npos p0) p H2).
intros.
split with x.
simpl in H5.
exact H5.
simpl in H2.
elim (H sigma (pre_ad_O pa) H3 (Npos p0) p H2).
intros.
split with x.
simpl in H5.
exact H5.
simpl in H2.
elim (H0 sigma (pre_ad_I pa) H4 N0 p H2).
intros.
split with x.
simpl in H5.
exact H5.
inversion H1.
Admitted.

Lemma st_compat_check_correct : forall (s : state) (sigma : signature), state_correct_wrt_sign s sigma -> st_compat_check s sigma = true.
Proof.
intros.
unfold st_compat_check in |- *.
apply (st_compat_check_0_correct s sigma pre_ad_empty).
unfold state_correct_wrt_sign_with_offset in |- *.
simpl in |- *.
Admitted.

Lemma st_compat_check_complete : forall (s : state) (sigma : signature), st_compat_check s sigma = true -> state_correct_wrt_sign s sigma.
Proof.
intros.
unfold state_correct_wrt_sign in |- *.
intros.
cut (state_correct_wrt_sign_with_offset s sigma pre_ad_empty).
intro.
unfold state_correct_wrt_sign_with_offset in H1.
elim (H1 a p H0).
intros.
split with x.
simpl in H2.
exact H2.
apply (st_compat_check_0_complete s sigma pre_ad_empty).
unfold st_compat_check in H.
Admitted.

Lemma predta_compat_check_correct : forall (d : preDTA) (sigma : signature), predta_correct_wrt_sign d sigma -> predta_compat_check d sigma = true.
Proof.
simple induction d.
intros.
reflexivity.
intros.
simpl in |- *.
unfold predta_correct_wrt_sign in H.
apply (st_compat_check_correct a0 sigma).
apply (H a a0).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
intros.
simpl in |- *.
rewrite (H sigma).
rewrite (H0 sigma).
reflexivity.
unfold predta_correct_wrt_sign in |- *.
unfold predta_correct_wrt_sign in H1.
intros.
apply (H1 (Ndouble_plus_one a) s).
induction a as [| p]; simpl in |- *; exact H2.
unfold predta_correct_wrt_sign in H1.
unfold predta_correct_wrt_sign in |- *.
intros.
apply (H1 (N.double a) s).
Admitted.

Lemma predta_compat_check_complete : forall (d : preDTA) (sigma : signature), predta_compat_check d sigma = true -> predta_correct_wrt_sign d sigma.
Proof.
simple induction d.
intros.
unfold predta_correct_wrt_sign in |- *.
intros.
inversion H0.
intros.
simpl in H.
unfold predta_correct_wrt_sign in |- *.
intros.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a1)); intros.
rewrite H1 in H0.
inversion H0.
rewrite H3 in H.
exact (st_compat_check_complete s sigma H).
rewrite H1 in H0.
inversion H0.
intros.
unfold predta_correct_wrt_sign in |- *.
simpl in H1.
elim (bool_is_true_or_false (predta_compat_check m sigma)); intros; rewrite H2 in H1.
elim (bool_is_true_or_false (predta_compat_check m0 sigma)); intros; rewrite H4 in H1.
unfold predta_correct_wrt_sign in H.
unfold predta_correct_wrt_sign in H0.
induction a as [| p].
simpl in H3.
exact (H sigma H2 _ _ H3).
induction p as [p Hrecp| p Hrecp| ]; simpl in H3.
exact (H0 _ H4 _ _ H3).
exact (H _ H2 _ _ H3).
exact (H0 _ H4 _ _ H3).
inversion H1.
Admitted.

Lemma dta_compat_check_correct : forall (d : DTA) (sigma : signature), dta_correct_wrt_sign d sigma -> dta_compat_check d sigma = true.
Proof.
simple induction d.
intro.
intro.
Admitted.

Lemma dta_compat_check_complete : forall (d : DTA) (sigma : signature), dta_compat_check d sigma = true -> dta_correct_wrt_sign d sigma.
Proof.
simple induction d.
intro.
intro.
Admitted.

Lemma st_compat_check_0_correct : forall (s : state) (sigma : signature) (pa : pre_ad), state_correct_wrt_sign_with_offset s sigma pa -> st_compat_check_0 pa sigma s = true.
Proof.
unfold state_correct_wrt_sign_with_offset in |- *.
simple induction s.
intros.
reflexivity.
intros.
simpl in |- *.
elim (H a a0).
intros.
elim H0.
intros.
rewrite (pl_compat_check_correct _ _ H2).
rewrite H1.
exact (beq_nat_correct x).
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
intros.
simpl in |- *.
rewrite (H sigma (pre_ad_O pa)).
rewrite (H0 sigma (pre_ad_I pa)).
reflexivity.
intros.
elim (H1 (Ndouble_plus_one a) p).
intros.
simpl in |- *.
split with x.
exact H3.
induction a as [| p0]; simpl in |- *; exact H2.
intros.
elim (H1 (N.double a) p).
intros.
simpl in |- *.
split with x.
exact H3.
induction a as [| p0]; simpl in |- *; exact H2.
