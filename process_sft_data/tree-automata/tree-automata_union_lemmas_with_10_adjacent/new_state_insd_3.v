Require Import Bool.
Require Import NArith Ndec Ndigits.
Require Import ZArith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Require Import refcorrect.
Definition uad_conv_0 (a : ad) : ad := match a with | N0 => N0 | Npos p => Npos (xO p) end.
Definition uad_conv_1 (a : ad) : ad := match a with | N0 => Npos 1 | Npos p => Npos (xI p) end.
Fixpoint upl_conv_0 (p : prec_list) : prec_list := match p with | prec_empty => prec_empty | prec_cons a p0 p1 => prec_cons (uad_conv_0 a) (upl_conv_0 p0) (upl_conv_0 p1) end.
Fixpoint upl_conv_1 (p : prec_list) : prec_list := match p with | prec_empty => prec_empty | prec_cons a p0 p1 => prec_cons (uad_conv_1 a) (upl_conv_1 p0) (upl_conv_1 p1) end.
Fixpoint umpl_conv_0 (s : state) : state := match s with | M0 => M0 prec_list | M1 a p => M1 prec_list a (upl_conv_0 p) | M2 p0 p1 => M2 prec_list (umpl_conv_0 p0) (umpl_conv_0 p1) end.
Fixpoint umpl_conv_1 (s : state) : state := match s with | M0 => M0 prec_list | M1 a p => M1 prec_list a (upl_conv_1 p) | M2 p0 p1 => M2 prec_list (umpl_conv_1 p0) (umpl_conv_1 p1) end.
Fixpoint udta_conv_0_aux (d : preDTA) : preDTA := match d with | M0 => M0 state | M1 a s => M1 state a (umpl_conv_0 s) | M2 s0 s1 => M2 state (udta_conv_0_aux s0) (udta_conv_0_aux s1) end.
Fixpoint udta_conv_1_aux (d : preDTA) : preDTA := match d with | M0 => M0 state | M1 a s => M1 state a (umpl_conv_1 s) | M2 s0 s1 => M2 state (udta_conv_1_aux s0) (udta_conv_1_aux s1) end.
Definition udta_conv_0 (d : preDTA) : preDTA := M2 state (udta_conv_0_aux d) (M0 state).
Definition udta_conv_1 (d : preDTA) : preDTA := M2 state (M0 state) (udta_conv_1_aux d).
Definition u_conv_rec_0 (p : preDTA) (a : ad) (t : term) (pr : reconnaissance p a t) := reconnaissance (udta_conv_0 p) (uad_conv_0 a) t.
Definition u_conv_str_0 (p : preDTA) (s : state) (t : term) (pr : state_reconnait p s t) := state_reconnait (udta_conv_0 p) (umpl_conv_0 s) t.
Definition u_conv_lr_0 (p : preDTA) (p0 : prec_list) (t : term_list) (pr : liste_reconnait p p0 t) := liste_reconnait (udta_conv_0 p) (upl_conv_0 p0) t.
Definition u_conv_rec_0_r (p0 : preDTA) (a0 : ad) (t : term) (pr0 : reconnaissance p0 a0 t) := forall (p : preDTA) (a : ad), p0 = udta_conv_0 p -> a0 = uad_conv_0 a -> reconnaissance p a t.
Definition u_conv_str_0_r (p0 : preDTA) (s0 : state) (t : term) (pr : state_reconnait p0 s0 t) := forall (p : preDTA) (s : state), p0 = udta_conv_0 p -> s0 = umpl_conv_0 s -> state_reconnait p s t.
Definition u_conv_lr_0_r (p0 : preDTA) (pl0 : prec_list) (t : term_list) (pr : liste_reconnait p0 pl0 t) := forall (p : preDTA) (pl : prec_list), p0 = udta_conv_0 p -> pl0 = upl_conv_0 pl -> liste_reconnait p pl t.
Definition u_conv_rec_1 (p : preDTA) (a : ad) (t : term) (pr : reconnaissance p a t) := reconnaissance (udta_conv_1 p) (uad_conv_1 a) t.
Definition u_conv_str_1 (p : preDTA) (s : state) (t : term) (pr : state_reconnait p s t) := state_reconnait (udta_conv_1 p) (umpl_conv_1 s) t.
Definition u_conv_lr_1 (p : preDTA) (p0 : prec_list) (t : term_list) (pr : liste_reconnait p p0 t) := liste_reconnait (udta_conv_1 p) (upl_conv_1 p0) t.
Definition u_conv_rec_1_r (p0 : preDTA) (a0 : ad) (t : term) (pr0 : reconnaissance p0 a0 t) := forall (p : preDTA) (a : ad), p0 = udta_conv_1 p -> a0 = uad_conv_1 a -> reconnaissance p a t.
Definition u_conv_str_1_r (p0 : preDTA) (s0 : state) (t : term) (pr : state_reconnait p0 s0 t) := forall (p : preDTA) (s : state), p0 = udta_conv_1 p -> s0 = umpl_conv_1 s -> state_reconnait p s t.
Definition u_conv_lr_1_r (p0 : preDTA) (pl0 : prec_list) (t : term_list) (pr : liste_reconnait p0 pl0 t) := forall (p : preDTA) (pl : prec_list), p0 = udta_conv_1 p -> pl0 = upl_conv_1 pl -> liste_reconnait p pl t.
Definition u_merge (p0 p1 : preDTA) : preDTA := MapMerge state (udta_conv_0 p0) (udta_conv_1 p1).
Definition u_merge_inv_0_dta (p0 : preDTA) (a : ad) (t : term) (pr : reconnaissance p0 a t) := forall p1 : preDTA, reconnaissance (u_merge p0 p1) (uad_conv_0 a) t.
Definition u_merge_inv_0_st (p0 : preDTA) (s : state) (t : term) (pr : state_reconnait p0 s t) := forall p1 : preDTA, state_reconnait (u_merge p0 p1) (umpl_conv_0 s) t.
Definition u_merge_inv_0_lst (p0 : preDTA) (pl : prec_list) (lt : term_list) (pr : liste_reconnait p0 pl lt) := forall p1 : preDTA, liste_reconnait (u_merge p0 p1) (upl_conv_0 pl) lt.
Definition u_merge_inv_1_dta (p1 : preDTA) (a : ad) (t : term) (pr : reconnaissance p1 a t) := forall p0 : preDTA, reconnaissance (u_merge p0 p1) (uad_conv_1 a) t.
Definition u_merge_inv_1_st (p1 : preDTA) (s : state) (t : term) (pr : state_reconnait p1 s t) := forall p0 : preDTA, state_reconnait (u_merge p0 p1) (umpl_conv_1 s) t.
Definition u_merge_inv_1_lst (p1 : preDTA) (pl : prec_list) (lt : term_list) (pr : liste_reconnait p1 pl lt) := forall p0 : preDTA, liste_reconnait (u_merge p0 p1) (upl_conv_1 pl) lt.
Definition u_merge_invr_0_dta (p : preDTA) (a : ad) (t : term) (pr : reconnaissance p a t) := forall p0 p1 : preDTA, p = u_merge p0 p1 -> forall a0 : ad, a = uad_conv_0 a0 -> reconnaissance (udta_conv_0 p0) a t.
Definition u_merge_invr_0_st (p : preDTA) (s : state) (t : term) (pr : state_reconnait p s t) := forall p0 p1 : preDTA, p = u_merge p0 p1 -> forall s0 : state, s = umpl_conv_0 s0 -> state_reconnait (udta_conv_0 p0) s t.
Definition u_merge_invr_0_lst (p : preDTA) (pl : prec_list) (lt : term_list) (pr : liste_reconnait p pl lt) := forall p0 p1 : preDTA, p = u_merge p0 p1 -> forall pl0 : prec_list, pl = upl_conv_0 pl0 -> liste_reconnait (udta_conv_0 p0) pl lt.
Definition u_merge_invr_1_dta (p : preDTA) (a : ad) (t : term) (pr : reconnaissance p a t) := forall p0 p1 : preDTA, p = u_merge p0 p1 -> forall a0 : ad, a = uad_conv_1 a0 -> reconnaissance (udta_conv_1 p1) a t.
Definition u_merge_invr_1_st (p : preDTA) (s : state) (t : term) (pr : state_reconnait p s t) := forall p0 p1 : preDTA, p = u_merge p0 p1 -> forall s0 : state, s = umpl_conv_1 s0 -> state_reconnait (udta_conv_1 p1) s t.
Definition u_merge_invr_1_lst (p : preDTA) (pl : prec_list) (lt : term_list) (pr : liste_reconnait p pl lt) := forall p0 p1 : preDTA, p = u_merge p0 p1 -> forall pl0 : prec_list, pl = upl_conv_1 pl0 -> liste_reconnait (udta_conv_1 p1) pl lt.
Fixpoint union_pl (pl0 : prec_list) : prec_list -> prec_list := fun pl1 : prec_list => match pl0 with | prec_empty => pl1 | prec_cons a pl00 pl01 => prec_cons a pl00 (union_pl pl01 pl1) end.
Fixpoint union_mpl_0 (c : ad) (pl : prec_list) (s : state) {struct s} : state := match s with | M0 => M1 prec_list c pl | M1 c0 pl0 => if N.eqb c c0 then M1 prec_list c (union_pl pl pl0) else MapMerge prec_list (M1 prec_list c pl) (M1 prec_list c0 pl0) | M2 s0 s1 => match c with | N0 => M2 prec_list (union_mpl_0 N0 pl s0) s1 | Npos p => match p with | xH => M2 prec_list s0 (union_mpl_0 N0 pl s1) | xO p' => M2 prec_list (union_mpl_0 (Npos p') pl s0) s1 | xI p' => M2 prec_list s0 (union_mpl_0 (Npos p') pl s1) end end end.
Fixpoint union_mpl (s0 : state) : state -> state := fun s1 : state => match s0, s1 with | M0, M0 => M0 prec_list | M0, M2 s10 s11 => M2 prec_list s10 s11 | _, M1 c1 pl1 => union_mpl_0 c1 pl1 s0 | M1 c0 pl0, _ => union_mpl_0 c0 pl0 s1 | M2 s00 s01, M0 => M2 prec_list s00 s01 | M2 s00 s01, M2 s10 s11 => M2 prec_list (union_mpl s00 s10) (union_mpl s01 s11) end.
Definition mpl_compat_7_def (s : state) : Prop := forall (c : ad) (pl l : prec_list), MapGet prec_list s c = Some l -> MapGet prec_list (union_mpl_0 c pl s) c = Some (union_pl pl l).
Definition mpl_compat_8_def (s : state) : Prop := forall (a c : ad) (pl l : prec_list), MapGet prec_list s c = Some l -> a <> c -> MapGet prec_list (union_mpl_0 a pl s) c = Some l.
Definition union_s_prd0 (s : state) : Prop := forall (d : preDTA) (c : ad) (pl : prec_list) (tl : term_list), mpl_compat (M1 prec_list c pl) s -> state_reconnait d (M1 prec_list c pl) (app c tl) -> state_reconnait d (union_mpl_0 c pl s) (app c tl).
Definition union_s_prd1 (s : state) : Prop := forall (d : preDTA) (a : ad) (pl : prec_list) (c : ad) (tl : term_list), mpl_compat (M1 prec_list a pl) s -> state_reconnait d s (app c tl) -> state_reconnait d (union_mpl_0 a pl s) (app c tl).
Definition union_std_def (s0 : state) : Prop := forall (s1 : state) (d : preDTA) (c : ad) (tl : term_list), mpl_compat s0 s1 -> state_reconnait d s0 (app c tl) -> state_reconnait d (union_mpl s0 s1) (app c tl) /\ state_reconnait d (union_mpl s1 s0) (app c tl).
Definition union_s_rpl_def (s : state) : Prop := forall (d : preDTA) (a : ad) (pl : prec_list) (c : ad) (tl : term_list), mpl_compat (M1 prec_list a pl) s -> state_reconnait d (union_mpl_0 a pl s) (app c tl) -> state_reconnait d (M1 prec_list a pl) (app c tl) \/ state_reconnait d s (app c tl).
Definition union_str_def (s0 : state) : Prop := forall (s1 : state) (d : preDTA) (c : ad) (tl : term_list), mpl_compat s0 s1 -> state_reconnait d (union_mpl s0 s1) (app c tl) \/ state_reconnait d (union_mpl s1 s0) (app c tl) -> state_reconnait d s0 (app c tl) \/ state_reconnait d s1 (app c tl).
Definition new_preDTA_ad : preDTA -> ad := ad_alloc_opt state.
Definition new_state_insd_def_dta (d : preDTA) (a0 : ad) (t0 : term) (pr : reconnaissance d a0 t0) := forall (a : ad) (s : state), MapGet state d a = None -> reconnaissance (MapPut state d a s) a0 t0.
Definition new_state_insd_def_st (d : preDTA) (s0 : state) (t0 : term) (pr : state_reconnait d s0 t0) := forall (a : ad) (s : state), MapGet state d a = None -> state_reconnait (MapPut state d a s) s0 t0.
Definition new_state_insd_def_lst (d : preDTA) (pl0 : prec_list) (tl0 : term_list) (pr : liste_reconnait d pl0 tl0) := forall (a : ad) (s : state), MapGet state d a = None -> liste_reconnait (MapPut state d a s) pl0 tl0.
Definition new_state_insr_def_dta (d0 : preDTA) (a0 : ad) (t0 : term) (pr : reconnaissance d0 a0 t0) := forall (d : preDTA) (a : ad) (s : state), preDTA_ref_ok d -> d0 = MapPut state d a s -> MapGet state d a = None -> a <> a0 -> reconnaissance d a0 t0.
Definition new_state_insr_def_st (d0 : preDTA) (s0 : state) (t0 : term) (pr : state_reconnait d0 s0 t0) := forall (d : preDTA) (a : ad) (s : state), preDTA_ref_ok d -> state_in_dta_diff d0 s0 a -> d0 = MapPut state d a s -> MapGet state d a = None -> state_reconnait d s0 t0.
Definition new_state_insr_def_lst (d0 : preDTA) (pl0 : prec_list) (tl0 : term_list) (pr : liste_reconnait d0 pl0 tl0) := forall (d : preDTA) (a : ad) (s : state), preDTA_ref_ok d -> d0 = MapPut state d a s -> MapGet state d a = None -> prec_in_dta_diff_cont d0 pl0 a -> liste_reconnait d pl0 tl0 /\ prec_in_dta_diff_cont d pl0 a.
Definition insert_state (d : preDTA) (a : ad) (s : state) : preDTA := MapPut state d a s.
Definition insert_main_state_0 (d : preDTA) (a : ad) (s : state) : DTA := dta (insert_state d a s) a.
Definition insert_main_state (d : preDTA) (s : state) : DTA := insert_main_state_0 d (new_preDTA_ad d) s.
Definition insert_ostate (d : preDTA) (a : ad) (o : option state) : preDTA := match o with | None => d | Some s => MapPut state d a s end.
Definition insert_main_ostate_0 (d : preDTA) (a : ad) (o : option state) : DTA := dta (insert_ostate d a o) a.
Definition insert_main_ostate (d : preDTA) (o : option state) : DTA := insert_main_ostate_0 d (new_preDTA_ad d) o.
Definition union_opt_state (o0 o1 : option state) : option state := match o0, o1 with | None, None => None | None, Some s1 => Some s1 | Some s0, None => Some s0 | Some s0, Some s1 => Some (union_mpl s0 s1) end.
Definition union_0 (d : preDTA) (a0 a1 : ad) : option state := union_opt_state (MapGet state d (uad_conv_0 a0)) (MapGet state d (uad_conv_1 a1)).
Definition union_1 (d : preDTA) (a0 a1 : ad) : DTA := insert_main_ostate d (union_0 d a0 a1).
Definition union (dt0 dt1 : DTA) : DTA := match dt0, dt1 with | dta d0 a0, dta d1 a1 => union_1 (u_merge d0 d1) a0 a1 end.

Lemma union_s_rpl : forall (s : state) (d : preDTA) (a : ad) (pl : prec_list) (c : ad) (tl : term_list), mpl_compat (M1 prec_list a pl) s -> state_reconnait d (union_mpl_0 a pl s) (app c tl) -> state_reconnait d (M1 prec_list a pl) (app c tl) \/ state_reconnait d s (app c tl).
Proof.
intro.
Admitted.

Lemma union_str_0 : union_str_def (M0 prec_list).
Proof.
unfold union_str_def in |- *.
intros.
induction s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
elim H0; intros.
inversion H1.
inversion H6.
inversion H1.
inversion H6.
simpl in H0.
right.
elim H0; intro; assumption.
simpl in H0.
right.
elim H0; intro.
assumption.
Admitted.

Lemma union_str_1 : forall (a : ad) (a0 : prec_list), union_str_def (M1 prec_list a a0).
Proof.
unfold union_str_def in |- *.
intros.
induction s1 as [| a1 a2| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
simpl in H0.
left.
elim H0; intro; assumption.
unfold union_mpl in H0.
elim H0; intros.
elim (union_s_rpl (M1 prec_list a a0) d a1 a2 c tl (mpl_compat_sym _ _ H) H1); intro.
right.
assumption.
left.
assumption.
elim (union_s_rpl (M1 prec_list a1 a2) d a a0 c tl H H1); intro.
left.
trivial.
right.
trivial.
elim H0; intros.
elim (union_s_rpl (M2 prec_list s1_1 s1_0) d a a0 c tl H H1).
intro.
left.
trivial.
right.
trivial.
Admitted.

Lemma union_str_2 : forall m : state, union_str_def m -> forall m0 : state, union_str_def m0 -> union_str_def (M2 prec_list m m0).
Proof.
unfold union_str_def in |- *.
intros.
induction s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
simpl in H2.
elim H2; intro; left; assumption.
unfold union_mpl in H2.
elim H2; intro.
elim (union_s_rpl (M2 prec_list m m0) d a a0 c tl (mpl_compat_sym _ _ H1) H3); intro.
right.
trivial.
left.
trivial.
elim (union_s_rpl (M2 prec_list m m0) d a a0 c tl (mpl_compat_sym _ _ H1) H3); intro.
right.
trivial.
left.
trivial.
cut (mpl_compat m s1_1).
cut (mpl_compat m0 s1_0).
intros.
induction c as [| p].
simpl in H2.
cut (state_reconnait d (union_mpl m s1_1) (app N0 tl) \/ state_reconnait d (union_mpl s1_1 m) (app N0 tl)).
intro.
elim (H s1_1 d N0 tl H4 H5); intro.
inversion H6.
left.
apply (rec_st d (M2 prec_list m m0) N0 tl l).
simpl in |- *.
assumption.
assumption.
right.
inversion H6.
apply (rec_st d (M2 prec_list s1_1 s1_0) N0 tl l).
simpl in |- *.
assumption.
assumption.
elim H2.
intro.
inversion H5.
left.
apply (rec_st d (union_mpl m s1_1) N0 tl l).
simpl in H10.
assumption.
assumption.
intro.
right.
inversion H5.
apply (rec_st d (union_mpl s1_1 m) N0 tl l).
simpl in H10.
assumption.
assumption.
induction p as [p Hrecp| p Hrecp| ].
simpl in H2.
clear Hrecp.
clear Hrecs1_1.
clear Hrecs1_0.
cut (state_reconnait d (union_mpl m0 s1_0) (app (Npos p) tl) \/ state_reconnait d (union_mpl s1_0 m0) (app (Npos p) tl)).
intro.
elim (H0 s1_0 d (Npos p) tl H3 H5).
intro.
left.
inversion H6.
apply (rec_st d (M2 prec_list m m0) (Npos (xI p)) tl l).
simpl in |- *.
assumption.
assumption.
intro.
inversion H6.
right.
apply (rec_st d (M2 prec_list s1_1 s1_0) (Npos (xI p)) tl l).
simpl in |- *.
assumption.
assumption.
elim H2; intro.
left.
inversion H5.
apply (rec_st d (union_mpl m0 s1_0) (Npos p) tl l).
simpl in H10.
assumption.
assumption.
inversion H5.
right.
apply (rec_st d (union_mpl s1_0 m0) (Npos p) tl l).
simpl in H10.
simpl in |- *.
assumption.
assumption.
clear Hrecp.
clear Hrecs1_1.
clear Hrecs1_0.
simpl in H2.
cut (state_reconnait d (union_mpl m s1_1) (app (Npos p) tl) \/ state_reconnait d (union_mpl s1_1 m) (app (Npos p) tl)).
intro.
elim (H s1_1 d (Npos p) tl H4 H5).
intro.
left.
inversion H6.
apply (rec_st d (M2 prec_list m m0) (Npos (xO p)) tl l).
simpl in |- *.
assumption.
assumption.
intro.
right.
inversion H6.
apply (rec_st d (M2 prec_list s1_1 s1_0) (Npos (xO p)) tl l).
simpl in |- *.
assumption.
assumption.
elim H2; intro; inversion H5.
left.
apply (rec_st d (union_mpl m s1_1) (Npos p) tl l).
simpl in H10.
assumption.
assumption.
right.
apply (rec_st d (union_mpl s1_1 m) (Npos p) tl l).
simpl in H10.
assumption.
assumption.
simpl in H2.
cut (state_reconnait d (union_mpl m0 s1_0) (app N0 tl) \/ state_reconnait d (union_mpl s1_0 m0) (app N0 tl)).
intro.
elim (H0 s1_0 d N0 tl H3 H5); intro.
inversion H6.
left.
apply (rec_st d (M2 prec_list m m0) (Npos 1) tl l).
simpl in |- *.
assumption.
assumption.
inversion H6.
right.
apply (rec_st d (M2 prec_list s1_1 s1_0) (Npos 1) tl l).
simpl in |- *.
assumption.
assumption.
elim H2; intro; inversion H5.
left.
simpl in H10.
apply (rec_st d (union_mpl m0 s1_0) N0 tl l).
assumption.
assumption.
right.
apply (rec_st d (union_mpl s1_0 m0) N0 tl l).
simpl in H10.
assumption.
assumption.
exact (mpl_compat_2 m m0 s1_1 s1_0 H1).
Admitted.

Lemma union_str_3 : forall m : state, union_str_def m.
Proof.
Admitted.

Lemma union_str : forall (s0 s1 : state) (d : preDTA) (c : ad) (tl : term_list), mpl_compat s0 s1 -> state_reconnait d (union_mpl s0 s1) (app c tl) \/ state_reconnait d (union_mpl s1 s0) (app c tl) -> state_reconnait d s0 (app c tl) \/ state_reconnait d s1 (app c tl).
Proof.
intro.
Admitted.

Lemma union_state : forall (s0 s1 : state) (d : preDTA) (t : term), mpl_compat s0 s1 -> (state_reconnait d (union_mpl s0 s1) t <-> state_reconnait d s0 t \/ state_reconnait d s1 t).
Proof.
intros.
split.
intro.
induction t as (a, t).
apply (union_str s0 s1 d a t H).
left.
trivial.
intro.
elim H0; intro.
induction t as (a, t).
elim (union_sd s0 s1 d a t H H1).
intros.
assumption.
induction t as (a, t).
elim (union_sd s1 s0 d a t (mpl_compat_sym _ _ H) H1).
intros.
Admitted.

Lemma new_state_insd_0 : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), new_state_insd_def_st d ladj t s -> new_state_insd_def_dta d a t (rec_dta d a t ladj e s).
Proof.
unfold new_state_insd_def_dta in |- *.
unfold new_state_insd_def_st in |- *.
intros.
apply (rec_dta (MapPut state d a0 s0) a t ladj).
rewrite (MapPut_semantics state d a0 s0 a).
elim (bool_is_true_or_false (N.eqb a0 a)); intros.
rewrite (Neqb_complete a0 a H1) in H0.
rewrite H0 in e.
inversion e.
rewrite H1.
assumption.
Admitted.

Lemma new_state_insd_1 : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), new_state_insd_def_lst d l tl l0 -> new_state_insd_def_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
unfold new_state_insd_def_lst in |- *.
unfold new_state_insd_def_st in |- *.
intros.
apply (rec_st (MapPut state d a s0) s c tl l).
assumption.
Admitted.

Lemma new_state_insd_2 : forall d : preDTA, new_state_insd_def_lst d prec_empty tnil (rec_empty d).
Proof.
unfold new_state_insd_def_lst in |- *.
intros.
Admitted.

Lemma new_state_insd_4 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)), new_state_insd_def_lst d ls (tcons hd tl) l -> new_state_insd_def_lst d (prec_cons a la ls) (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
unfold new_state_insd_def_lst in |- *.
intros.
Admitted.

Lemma new_state_insd_5 : forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t), new_state_insd_def_dta p a t r.
Proof.
Admitted.

Lemma new_state_ins_d : forall (d : preDTA) (a : ad) (s : state) (a0 : ad) (t : term), reconnaissance d a0 t -> MapGet state d a = None -> reconnaissance (MapPut state d a s) a0 t.
Proof.
intros.
Admitted.

Lemma new_state_insr_0 : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), new_state_insr_def_st d ladj t s -> new_state_insr_def_dta d a t (rec_dta d a t ladj e s).
Proof.
unfold new_state_insr_def_st in |- *.
unfold new_state_insr_def_dta in |- *.
intros.
apply (rec_dta d0 a t ladj).
rewrite H1 in e.
rewrite (MapPut_semantics state d0 a0 s0) in e.
elim (bool_is_true_or_false (N.eqb a0 a)); intro.
elim (H3 (Neqb_complete _ _ H4)).
rewrite H4 in e.
assumption.
apply (H d0 a0 s0).
assumption.
unfold state_in_dta_diff in |- *.
split with a.
split; assumption.
assumption.
Admitted.

Lemma new_state_insr_1 : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), new_state_insr_def_lst d l tl l0 -> new_state_insr_def_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
unfold new_state_insr_def_lst in |- *.
intros.
unfold new_state_insr_def_st in |- *.
intros.
cut (prec_in_dta_diff_cont d l a).
intro.
elim (H d0 a s0 H0 H2 H3 H4).
intros.
apply (rec_st d0 s c tl l).
assumption.
assumption.
unfold prec_in_dta_diff_cont in |- *.
split with s.
elim H1.
intros.
split with x.
elim H4; intros.
split with c.
split with l.
split.
assumption.
split.
assumption.
split.
exact (prec_id _).
Admitted.

Lemma new_state_insr_2 : forall d : preDTA, new_state_insr_def_lst d prec_empty tnil (rec_empty d).
Proof.
intros.
unfold new_state_insr_def_lst in |- *.
intros.
split.
exact (rec_empty d0).
unfold prec_in_dta_diff_cont in |- *.
unfold prec_in_dta_diff_cont in H1.
elim H1.
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H8.
intros.
elim H10.
intros.
split with x.
split with x0.
split with x1.
split with x2.
split.
simpl in H7.
rewrite H0 in H7.
rewrite (MapPut_semantics state d0 a s) in H7.
elim (bool_is_true_or_false (N.eqb a x0)); intro.
elim (H12 (Neqb_complete _ _ H13)).
rewrite H13 in H7.
assumption.
split.
assumption.
Admitted.

Lemma new_state_insr_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), new_state_insr_def_dta d a hd r -> forall l : liste_reconnait d la tl, new_state_insr_def_lst d la tl l -> new_state_insr_def_lst d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
unfold new_state_insr_def_lst in |- *.
unfold new_state_insr_def_dta in |- *.
intros.
split.
apply (rec_consi d0 a la ls hd tl).
cut (a0 <> a).
intro.
exact (H d0 a0 s H1 H2 H3 H5).
unfold prec_in_dta_diff_cont in H4.
unfold preDTA_ref_ok in H1.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H8.
intros.
elim H10.
intros.
cut (MapGet state d0 x0 = Some x).
cut (prec_occur x2 a).
intros.
elim (H1 x0 x x1 x2 a H14 H11 H13).
intros.
elim (classic (a0 = a)).
intro.
rewrite <- H16 in H15.
rewrite H15 in H3.
inversion H3.
intro.
assumption.
elim H12.
intros.
exact (prec_occur_1 a la ls x2 H13).
rewrite H2 in H9.
rewrite (MapPut_semantics state d0 a0 s) in H9.
elim (bool_is_true_or_false (N.eqb a0 x0)).
intro.
elim H12.
intros.
elim (H15 (Neqb_complete _ _ H13)).
intros.
rewrite H13 in H9.
assumption.
unfold prec_in_dta_diff_cont in H4.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H8.
intros.
elim H10.
intros.
elim H12.
intros.
cut (prec_in_dta_diff_cont d la a0).
intro.
elim (H0 d0 a0 s H1 H2 H3 H15).
intros.
assumption.
unfold prec_in_dta_diff_cont in |- *.
split with x.
split with x0.
split with x1.
split with x2.
split.
assumption.
split.
assumption.
split.
exact (prec_contained_0 _ _ _ _ H13).
assumption.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H8.
intros.
elim H10.
intros.
elim H12.
intros.
rewrite H2 in H9.
rewrite (MapPut_semantics state d0 a0 s) in H9.
elim (bool_is_true_or_false (N.eqb a0 x0)); intro.
elim (H14 (Neqb_complete _ _ H15)).
rewrite H15 in H9.
split with x.
split with x0.
split with x1.
split with x2.
split.
assumption.
split.
assumption.
Admitted.

Lemma new_state_insr_4 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)), new_state_insr_def_lst d ls (tcons hd tl) l -> new_state_insr_def_lst d (prec_cons a la ls) (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
unfold new_state_insr_def_lst in |- *.
intros.
split.
apply (rec_consn d0 a la ls hd tl).
cut (prec_in_dta_diff_cont d ls a0).
intro.
elim (H d0 a0 s H0 H1 H2 H4).
intros.
assumption.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
elim H11.
intros.
split with x.
split with x0.
split with x1.
split with x2.
split.
assumption.
split.
assumption.
split.
exact (prec_contained_1 a la ls x2 H12).
assumption.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
elim H11.
intros.
split with x.
split with x0.
split with x1.
split with x2.
split.
rewrite H1 in H8.
rewrite (MapPut_semantics state d0 a0 s) in H8.
elim (bool_is_true_or_false (N.eqb a0 x0)); intro.
elim (H13 (Neqb_complete _ _ H14)).
rewrite H14 in H8.
assumption.
split.
assumption.
Admitted.

Lemma new_state_insr_5 : forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t), new_state_insr_def_dta p a t r.
Proof.
Admitted.

Lemma new_state_ins_r : forall (d0 : preDTA) (a0 : ad) (t0 : term) (d : preDTA) (a : ad) (s : state), reconnaissance d0 a0 t0 -> preDTA_ref_ok d -> d0 = MapPut state d a s -> MapGet state d a = None -> a <> a0 -> reconnaissance d a0 t0.
Proof.
intros.
Admitted.

Lemma new_state_insd_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), new_state_insd_def_dta d a hd r -> forall l : liste_reconnait d la tl, new_state_insd_def_lst d la tl l -> new_state_insd_def_lst d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
unfold new_state_insd_def_lst in |- *.
unfold new_state_insd_def_dta in |- *.
intros.
apply (rec_consi (MapPut state d a0 s) a la ls hd tl).
exact (H a0 s H1).
exact (H0 a0 s H1).
