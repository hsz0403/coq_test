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

Lemma pl_tl_length_rec_5 : forall n : nat, pl_tl_length_rec_def_0 n -> pl_tl_length_rec_def_0 (S n).
Proof.
intros.
unfold pl_tl_length_rec_def_0 in |- *.
intros.
Admitted.

Lemma pl_tl_length_rec_6 : forall (d : preDTA) (pl : prec_list) (tl : term_list) (n : nat), pl_tl_length pl n -> liste_reconnait d pl tl -> n = lst_length tl.
Proof.
intros.
Admitted.

Lemma pl_compatible_sym : forall pl0 pl1 : prec_list, pl_compatible pl0 pl1 -> pl_compatible pl1 pl0.
Proof.
unfold pl_compatible in |- *.
intros.
elim H.
intros.
elim H0.
intros.
split with x.
Admitted.

Lemma pl_compatible_empt_l : forall p : prec_list, pl_compatible prec_empty p -> p = prec_empty.
Proof.
intros.
Admitted.

Lemma pl_compatible_cons_r : forall (p : prec_list) (a : ad) (la ls : prec_list), pl_compatible p (prec_cons a la ls) -> exists a0 : ad, (exists la0 : prec_list, (exists ls0 : prec_list, p = prec_cons a0 la0 ls0)).
Proof.
intros.
unfold pl_compatible in H.
elim H.
intros.
elim H0.
intros.
elim (pl_sum p).
intro.
rewrite H3 in H1.
inversion H1.
rewrite <- H5 in H2.
inversion H2.
intro.
Admitted.

Lemma pl_compatible_cons_l : forall (p : prec_list) (a : ad) (la ls : prec_list), pl_compatible (prec_cons a la ls) p -> exists a0 : ad, (exists la0 : prec_list, (exists ls0 : prec_list, p = prec_cons a0 la0 ls0)).
Proof.
intros.
Admitted.

Lemma pl_compatible_compat : forall p0 p1 : prec_list, pl_compatible p0 p1 -> pl_compat p0 p1.
Proof.
simple induction p0.
intros.
elim (pl_compatible_cons_l _ _ _ _ H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H4.
unfold pl_compat in |- *.
right.
split; intro; inversion H5.
intros.
elim (pl_compatible_empt_l _ H).
unfold pl_compat in |- *.
induction p1 as [a p1_1 Hrecp1_1 p1_0 Hrecp1_0| ].
right.
split; intro; inversion H0.
left.
Admitted.

Lemma st_compatible_compat_0 : st_compatible_compat_def (M0 prec_list).
Proof.
unfold st_compatible_compat_def in |- *.
intros.
unfold mpl_compat in |- *.
intros.
Admitted.

Lemma st_compatible_compat_1 : forall (a : ad) (a0 : prec_list), st_compatible_compat_def (M1 prec_list a a0).
Proof.
unfold st_compatible_compat_def in |- *.
intros.
unfold mpl_compat in |- *.
intros.
induction s1 as [| a1 a2| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
inversion H1.
unfold st_compatible in |- *.
unfold st_compatible in H.
exact (pl_compatible_compat _ _ (H _ _ _ H0 H1)).
unfold st_compatible in H.
Admitted.

Lemma st_compatible_compat_2 : forall m : Map prec_list, st_compatible_compat_def m -> forall m0 : Map prec_list, st_compatible_compat_def m0 -> st_compatible_compat_def (M2 prec_list m m0).
Proof.
unfold st_compatible_compat_def in |- *.
unfold mpl_compat in |- *.
intros.
induction s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
inversion H3.
induction a as [| p].
induction c as [| p].
simpl in H2.
apply (H (M1 prec_list N0 a0)) with (c := N0) (p0 := p0) (p1 := p1).
unfold st_compatible in |- *.
intros.
unfold st_compatible in H1.
apply (H1 N0 pl0 pl1).
simpl in |- *.
induction c as [| p].
exact H4.
inversion H5.
simpl in |- *.
induction c as [| p].
simpl in H5.
exact H5.
inversion H5.
exact H2.
exact H3.
inversion H3.
induction c as [| p2].
inversion H3.
simpl in H3.
elim (bool_is_true_or_false (Pos.eqb p p2)); intro; rewrite H4 in H3; inversion H3.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
simpl in H2.
apply (H0 (M1 prec_list (Npos p2) p1)) with (c := Npos p2) (p0 := p0) (p3 := p1).
unfold st_compatible in H1.
unfold st_compatible in |- *.
intros.
simpl in H7.
rewrite (aux_Neqb_1_1 _ _ H4) in H1.
apply (H1 (Npos (xI p2)) pl0 pl1).
simpl in |- *.
elim (N.discr c); intro y.
elim y.
intros x y0.
rewrite y0 in H7.
elim (bool_is_true_or_false (Pos.eqb p2 x)); intro; rewrite H8 in H7.
rewrite <- (aux_Neqb_1_1 _ _ H8) in y0.
rewrite y0 in H5.
exact H5.
inversion H7.
rewrite y in H7.
inversion H7.
simpl in |- *.
rewrite (aux_Neqb_1_0 p2).
inversion H3.
induction c as [| p3].
inversion H7.
elim (bool_is_true_or_false (Pos.eqb p2 p3)); intro; rewrite H8 in H7.
exact H7.
inversion H7.
exact H2.
simpl in |- *.
rewrite (aux_Neqb_1_0 p2).
reflexivity.
apply (H (M1 prec_list (Npos p2) a0)) with (c := Npos p2) (p0 := p0) (p1 := p1).
unfold st_compatible in |- *.
unfold st_compatible in H1.
intros.
apply (H1 (Npos (xO p2)) pl0 pl1).
simpl in |- *.
simpl in H2.
induction c as [| p3]; simpl in H7.
inversion H7.
elim (bool_is_true_or_false (Pos.eqb p2 p3)); intro; rewrite H8 in H7.
rewrite <- (aux_Neqb_1_1 _ _ H8) in H5.
exact H5.
inversion H7.
rewrite (aux_Neqb_1_1 _ _ H4).
simpl in |- *.
rewrite (aux_Neqb_1_0 p2).
simpl in H7.
induction c as [| p3].
inversion H7.
elim (bool_is_true_or_false (Pos.eqb p2 p3)); intro; rewrite H8 in H7.
inversion H7.
reflexivity.
inversion H7.
simpl in H2.
exact H2.
simpl in |- *.
rewrite (aux_Neqb_1_0 p2).
exact H3.
apply (H0 (M1 prec_list N0 a0)) with (c := N0) (p0 := p0) (p1 := p1).
unfold st_compatible in |- *.
unfold st_compatible in H1.
intros.
induction c as [| p2].
apply (H1 (Npos 1) pl0 pl1).
simpl in |- *.
simpl in H2.
exact H5.
simpl in |- *.
rewrite (aux_Neqb_1_1 _ _ H4).
simpl in H7.
exact H7.
inversion H7.
simpl in H2.
exact H2.
simpl in |- *.
exact H3.
cut (st_compatible m s1_1).
cut (st_compatible m0 s1_0).
intros.
induction c as [| p]; simpl in H2; simpl in H3.
exact (H _ H5 _ _ _ H2 H3).
induction p as [p Hrecp| p Hrecp| ].
exact (H0 _ H4 _ _ _ H2 H3).
exact (H _ H5 _ _ _ H2 H3).
exact (H0 _ H4 _ _ _ H2 H3).
unfold st_compatible in |- *.
unfold st_compatible in H1.
intros.
apply (H1 (Ndouble_plus_one c0) pl0 pl1).
induction c0 as [| p]; simpl in |- *; exact H4.
induction c0 as [| p]; simpl in |- *; exact H5.
unfold st_compatible in |- *.
unfold st_compatible in H1.
intros.
apply (H1 (N.double c0) pl0 pl1).
induction c0 as [| p]; simpl in |- *; assumption.
Admitted.

Lemma st_compatible_compat : forall s0 s1 : state, st_compatible s0 s1 -> mpl_compat s0 s1.
Proof.
Admitted.

Lemma predta_compatible_compat_0 : predta_compatible_compat_def (M0 state).
Proof.
unfold predta_compatible_compat_def in |- *.
intros.
unfold dta_compat in |- *.
intros.
Admitted.

Lemma predta_compatible_compat_1 : forall (a : ad) (a0 : state), predta_compatible_compat_def (M1 state a a0).
Proof.
unfold predta_compatible_compat_def in |- *.
intros.
unfold dta_compat in |- *.
unfold predta_compatible in H.
intros.
induction d1 as [| a3 a4| d1_1 Hrecd1_1 d1_0 Hrecd1_0].
inversion H1.
apply (st_compatible_compat s0 s1).
apply (H s0 s1).
split with a1.
assumption.
split with a2.
assumption.
apply (st_compatible_compat s0 s1).
apply (H s0 s1).
split with a1.
exact H0.
split with a2.
Admitted.

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

Lemma pl_compatible_empt_r : forall p : prec_list, pl_compatible p prec_empty -> p = prec_empty.
Proof.
unfold pl_compatible in |- *.
intros.
elim H.
intros.
elim H0.
intros.
inversion H2.
rewrite <- H4 in H1.
inversion H1.
reflexivity.
