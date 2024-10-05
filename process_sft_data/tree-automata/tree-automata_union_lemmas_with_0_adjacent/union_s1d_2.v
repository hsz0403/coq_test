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

Lemma union_s1d_2 : forall m : state, union_s_prd1 m -> forall m0 : state, union_s_prd1 m0 -> union_s_prd1 (M2 prec_list m m0).
Proof.
unfold union_s_prd1 in |- *.
intros.
induction c as [| p].
induction a as [| p].
simpl in |- *.
cut (state_reconnait d (union_mpl_0 N0 pl m) (app N0 tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) N0 tl l).
simpl in |- *.
assumption.
assumption.
apply (H d N0 pl N0 tl).
apply (mpl_compat_sym m (M1 prec_list N0 pl)).
apply (mpl_compat_3 m m0 pl).
exact (mpl_compat_sym (M1 prec_list N0 pl) (M2 prec_list m m0) H1).
inversion H2.
apply (rec_st d m N0 tl l).
simpl in H7.
assumption.
assumption.
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
inversion H2.
apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p) pl m0)) N0 tl l).
simpl in |- *.
simpl in H7.
assumption.
assumption.
simpl in |- *.
cut (state_reconnait d (union_mpl_0 (Npos p) pl m) (app N0 tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p) pl m) m0) N0 tl l).
simpl in |- *.
assumption.
assumption.
apply (H d (Npos p) pl N0 tl).
apply (mpl_compat_sym m (M1 prec_list (Npos p) pl)).
apply (mpl_compat_5 m m0 pl p).
exact (mpl_compat_sym (M1 prec_list (Npos (xO p)) pl) (M2 prec_list m m0) H1).
inversion H2.
simpl in H7.
exact (rec_st d m N0 tl l H7 H8).
simpl in |- *.
inversion H2.
apply (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) N0 tl l).
simpl in |- *.
simpl in H7.
assumption.
assumption.
induction p as [p Hrecp| p Hrecp| ].
induction a as [| p0].
simpl in |- *.
inversion H2.
apply (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) (Npos (xI p)) tl l).
simpl in |- *.
simpl in H7.
assumption.
assumption.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
cut (state_reconnait d (union_mpl_0 (Npos p0) pl m0) (app (Npos p) tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p0) pl m0)) (Npos (xI p)) tl l).
simpl in |- *.
assumption.
assumption.
apply (H0 d (Npos p0) pl (Npos p) tl).
apply (mpl_compat_sym m0 (M1 prec_list (Npos p0) pl)).
apply (mpl_compat_6 m m0 pl p0).
exact (mpl_compat_sym (M1 prec_list (Npos (xI p0)) pl) (M2 prec_list m m0) H1).
inversion H2.
simpl in H7.
exact (rec_st d m0 (Npos p) tl l H7 H8).
simpl in |- *.
inversion H2.
apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p0) pl m) m0) (Npos (xI p)) tl l).
simpl in |- *.
simpl in H7.
assumption.
assumption.
simpl in |- *.
cut (state_reconnait d (union_mpl_0 N0 pl m0) (app (Npos p) tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) (Npos (xI p)) tl l).
simpl in |- *.
assumption.
assumption.
apply (H0 d N0 pl (Npos p) tl).
apply (mpl_compat_sym m0 (M1 prec_list N0 pl)).
apply (mpl_compat_4 m m0 pl).
exact (mpl_compat_sym (M1 prec_list (Npos 1) pl) (M2 prec_list m m0) H1).
inversion H2.
simpl in H7.
exact (rec_st d m0 (Npos p) tl l H7 H8).
induction a as [| p0].
simpl in |- *.
cut (state_reconnait d (union_mpl_0 N0 pl m) (app (Npos p) tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) (Npos (xO p)) tl l).
simpl in |- *.
assumption.
assumption.
apply (H d N0 pl (Npos p) tl).
apply (mpl_compat_sym m (M1 prec_list N0 pl)).
apply (mpl_compat_3 m m0 pl).
exact (mpl_compat_sym (M1 prec_list N0 pl) (M2 prec_list m m0) H1).
inversion H2.
simpl in H7.
exact (rec_st d m (Npos p) tl l H7 H8).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
inversion H2.
apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p0) pl m0)) (Npos (xO p)) tl l).
simpl in |- *.
simpl in H7.
assumption.
assumption.
simpl in |- *.
cut (state_reconnait d (union_mpl_0 (Npos p0) pl m) (app (Npos p) tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p0) pl m) m0) (Npos (xO p)) tl l).
simpl in |- *.
simpl in H8.
assumption.
assumption.
apply (H d (Npos p0) pl (Npos p) tl).
apply (mpl_compat_sym m (M1 prec_list (Npos p0) pl)).
apply (mpl_compat_5 m m0 pl p0).
exact (mpl_compat_sym (M1 prec_list (Npos (xO p0)) pl) (M2 prec_list m m0) H1).
inversion H2.
simpl in H7.
exact (rec_st d m (Npos p) tl l H7 H8).
simpl in |- *.
inversion H2.
simpl in H7.
apply (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) (Npos (xO p)) tl l).
simpl in |- *.
assumption.
assumption.
induction a as [| p].
simpl in |- *.
inversion H2.
simpl in H7.
apply (rec_st d (M2 prec_list (union_mpl_0 N0 pl m) m0) (Npos 1) tl l).
simpl in |- *.
assumption.
assumption.
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
cut (state_reconnait d (union_mpl_0 (Npos p) pl m0) (app N0 tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list m (union_mpl_0 (Npos p) pl m0)) (Npos 1) tl l).
simpl in |- *.
simpl in H8.
assumption.
assumption.
apply (H0 d (Npos p) pl N0 tl).
apply (mpl_compat_sym m0 (M1 prec_list (Npos p) pl)).
apply (mpl_compat_6 m m0 pl p).
exact (mpl_compat_sym (M1 prec_list (Npos (xI p)) pl) (M2 prec_list m m0) H1).
inversion H2.
simpl in H7.
exact (rec_st d m0 N0 tl l H7 H8).
simpl in |- *.
inversion H2.
simpl in H7.
apply (rec_st d (M2 prec_list (union_mpl_0 (Npos p) pl m) m0) (Npos 1) tl l).
simpl in |- *.
assumption.
assumption.
simpl in |- *.
cut (state_reconnait d (union_mpl_0 N0 pl m0) (app N0 tl)).
intro.
inversion H3.
apply (rec_st d (M2 prec_list m (union_mpl_0 N0 pl m0)) (Npos 1) tl l).
simpl in |- *.
assumption.
assumption.
apply (H0 d N0 pl N0 tl).
apply (mpl_compat_sym m0 (M1 prec_list N0 pl)).
apply (mpl_compat_4 m m0 pl).
exact (mpl_compat_sym (M1 prec_list (Npos 1) pl) (M2 prec_list m m0) H1).
inversion H2.
simpl in H7.
exact (rec_st d m0 N0 tl l H7 H8).
