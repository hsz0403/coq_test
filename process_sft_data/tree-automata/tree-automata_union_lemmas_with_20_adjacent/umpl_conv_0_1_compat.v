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

Lemma insert_ostate_2 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s s0 s1 s0' s1' : state) (t : term), MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> preDTA_ref_ok (u_merge d0 d1) -> MapGet state (u_merge d0 d1) a = None -> a <> uad_conv_1 a1 -> (reconnaissance d1 a1 t <-> reconnaissance (insert_ostate (u_merge d0 d1) a (Some s)) (uad_conv_1 a1) t).
Proof.
intros.
cut (reconnaissance (u_merge d0 d1) (uad_conv_1 a1) t <-> reconnaissance (insert_ostate (u_merge d0 d1) a (Some s)) (uad_conv_1 a1) t).
intro.
elim H6.
intros.
split.
intros.
apply H7.
exact (u_merge_3 d0 d1 a1 t H9).
intro.
exact (u_merge_5 d0 d1 a1 t (H8 H9)).
Admitted.

Lemma insert_ostate_3 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s s0 s1 s0' s1' : state) (t : term), MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> preDTA_ref_ok (u_merge d0 d1) -> MapGet state (u_merge d0 d1) a = None -> a <> uad_conv_0 a0 -> (reconnaissance (insert_ostate (u_merge d0 d1) a (Some s)) (uad_conv_0 a0) t <-> state_reconnait (insert_ostate (u_merge d0 d1) a (Some s)) s0' t).
Proof.
intros.
split.
intro.
inversion H6.
unfold insert_ostate in H7.
rewrite (MapPut_semantics state (u_merge d0 d1) a s) in H7.
elim (bool_is_true_or_false (N.eqb a (uad_conv_0 a0))); intro.
elim (H5 (Neqb_complete _ _ H12)).
rewrite H12 in H7.
induction t as (a3, t).
inversion H8.
apply (rec_st (insert_ostate (u_merge d0 d1) a (Some s)) s0' a3 t l).
rewrite H7 in H1.
inversion H1.
rewrite <- H20.
assumption.
assumption.
intro.
apply (rec_dta (insert_ostate (u_merge d0 d1) a (Some s)) (uad_conv_0 a0) t s0').
unfold insert_ostate in |- *.
rewrite (MapPut_semantics state (u_merge d0 d1) a s).
elim (bool_is_true_or_false (N.eqb a (uad_conv_0 a0))); intro.
elim (H5 (Neqb_complete _ _ H7)).
rewrite H7.
assumption.
Admitted.

Lemma insert_ostate_4 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s s0 s1 s0' s1' : state) (t : term), MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> preDTA_ref_ok (u_merge d0 d1) -> MapGet state (u_merge d0 d1) a = None -> a <> uad_conv_1 a1 -> (reconnaissance (insert_ostate (u_merge d0 d1) a (Some s)) (uad_conv_1 a1) t <-> state_reconnait (insert_ostate (u_merge d0 d1) a (Some s)) s1' t).
Proof.
intros.
split.
intro.
inversion H6.
unfold insert_ostate in H7.
rewrite (MapPut_semantics state (u_merge d0 d1) a s) in H7.
elim (bool_is_true_or_false (N.eqb a (uad_conv_1 a1))); intro.
elim (H5 (Neqb_complete _ _ H12)).
rewrite H12 in H7.
induction t as (a3, t).
inversion H8.
apply (rec_st (insert_ostate (u_merge d0 d1) a (Some s)) s1' a3 t l).
rewrite H7 in H2.
inversion H2.
rewrite <- H20.
assumption.
assumption.
intro.
apply (rec_dta (insert_ostate (u_merge d0 d1) a (Some s)) (uad_conv_1 a1) t s1').
unfold insert_ostate in |- *.
rewrite (MapPut_semantics state (u_merge d0 d1) a s).
elim (bool_is_true_or_false (N.eqb a (uad_conv_1 a1))); intro.
elim (H5 (Neqb_complete _ _ H7)).
rewrite H7.
assumption.
Admitted.

Lemma insert_ostate_5 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term), mpl_compat s0' s1' -> MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> preDTA_ref_ok (u_merge d0 d1) -> MapGet state (u_merge d0 d1) a = None -> a <> uad_conv_0 a0 -> a <> uad_conv_1 a1 -> (state_reconnait (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) (union_mpl s0' s1') t <-> state_reconnait (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) s0' t \/ state_reconnait (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) s1' t).
Proof.
intros.
Admitted.

Lemma insert_ostate_6 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term), mpl_compat s0' s1' -> MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> preDTA_ref_ok (u_merge d0 d1) -> MapGet state (u_merge d0 d1) a = None -> a <> uad_conv_0 a0 -> a <> uad_conv_1 a1 -> (state_reconnait (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) (union_mpl s0' s1') t <-> reconnaissance (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
intros.
split.
intro.
apply (rec_dta (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t (union_mpl s0' s1')).
unfold insert_ostate in |- *.
rewrite (MapPut_semantics state (u_merge d0 d1) a (union_mpl s0' s1')).
rewrite (Neqb_correct a).
trivial.
assumption.
intro.
inversion H8.
unfold insert_ostate in H9.
rewrite (MapPut_semantics state (u_merge d0 d1) a (union_mpl s0' s1')) in H9.
rewrite (Neqb_correct a) in H9.
inversion H9.
rewrite <- H15 in H10.
Admitted.

Lemma insert_ostate_7 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term), mpl_compat s0' s1' -> MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> preDTA_ref_ok (u_merge d0 d1) -> MapGet state (u_merge d0 d1) a = None -> a <> uad_conv_0 a0 -> a <> uad_conv_1 a1 -> (reconnaissance d0 a0 t \/ reconnaissance d1 a1 t <-> reconnaissance (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
intros.
elim (insert_ostate_1 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2 H3 H4 H5 H6).
elim (insert_ostate_2 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2 H3 H4 H5 H7).
intros.
elim (insert_ostate_3 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2 H3 H4 H5 H6).
elim (insert_ostate_4 d0 d1 a0 a1 a (union_mpl s0' s1') s0 s1 s0' s1' t H0 H1 H2 H3 H4 H5 H7).
intros.
elim (insert_ostate_5 d0 d1 a0 a1 a s0 s1 s0' s1' t H H0 H1 H2 H3 H4 H5 H6 H7).
elim (insert_ostate_6 d0 d1 a0 a1 a s0 s1 s0' s1' t H H0 H1 H2 H3 H4 H5 H6 H7).
intros.
split.
intro.
apply H16.
apply H19.
elim H20; intro.
left.
exact (H14 (H10 H21)).
right.
exact (H12 (H8 H21)).
intro.
elim (H18 (H17 H20)).
intro.
left.
exact (H11 (H15 H21)).
intro.
right.
Admitted.

Lemma insert_ostate_8 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0 s1 s0' s1' : state) (t : term), mpl_compat s0' s1' -> MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> preDTA_ref_ok (u_merge d0 d1) -> a = new_preDTA_ad (u_merge d0 d1) -> (reconnaissance d0 a0 t \/ reconnaissance d1 a1 t <-> reconnaissance (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
intros.
apply (insert_ostate_7 d0 d1 a0 a1 a s0 s1 s0' s1' t H H0 H1 H2 H3 H4).
unfold new_preDTA_ad in H5.
rewrite H5.
exact (ad_alloc_opt_allocates_1 state (u_merge d0 d1)).
intro.
rewrite H5 in H6.
rewrite <- H6 in H2.
unfold new_preDTA_ad in H2.
rewrite (ad_alloc_opt_allocates_1 state (u_merge d0 d1)) in H2.
inversion H2.
intro.
rewrite H5 in H6.
rewrite <- H6 in H3.
unfold new_preDTA_ad in H3.
rewrite (ad_alloc_opt_allocates_1 state (u_merge d0 d1)) in H3.
Admitted.

Lemma upl_conv_0_occur : forall (pl : prec_list) (a : ad), prec_occur (upl_conv_0 pl) (uad_conv_0 a) -> prec_occur pl a.
Proof.
simple induction pl.
intros.
simpl in H1.
inversion H1.
rewrite (adcnv_inj0 a a0 H6).
exact (prec_hd a0 p p0).
exact (prec_int0 a a0 p p0 (H a0 H6)).
exact (prec_int1 a a0 p p0 (H0 a0 H6)).
intros.
simpl in H.
Admitted.

Lemma upl_conv_1_occur : forall (pl : prec_list) (a : ad), prec_occur (upl_conv_1 pl) (uad_conv_1 a) -> prec_occur pl a.
Proof.
simple induction pl.
intros.
simpl in H1.
inversion H1.
rewrite (adcnv_inj1 a a0 H6).
exact (prec_hd a0 p p0).
exact (prec_int0 a a0 p p0 (H a0 H6)).
exact (prec_int1 a a0 p p0 (H0 a0 H6)).
intros.
simpl in H.
Admitted.

Lemma upl_conv_0_occur_in_img : forall (pl : prec_list) (a : ad), prec_occur (upl_conv_0 pl) a -> exists b : ad, a = uad_conv_0 b.
Proof.
simple induction pl.
intros.
simpl in H1.
inversion H1.
split with a.
trivial.
elim (H a0 H6).
intros.
split with x.
trivial.
elim (H0 a0 H6).
intros.
split with x.
trivial.
intros.
Admitted.

Lemma upl_conv_1_occur_in_img : forall (pl : prec_list) (a : ad), prec_occur (upl_conv_1 pl) a -> exists b : ad, a = uad_conv_1 b.
Proof.
simple induction pl.
intros.
simpl in H1.
inversion H1.
split with a.
trivial.
elim (H a0 H6).
intros.
split with x.
trivial.
elim (H0 a0 H6).
intros.
split with x.
trivial.
intros.
Admitted.

Lemma u_conv_0_ref_ok : forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_0 d).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
elim (u_conv_0_invar_8 d a s H0).
intros.
rewrite H3 in H0.
elim (u_conv_0_invar_5 d x s H0).
intros.
elim H4.
intros.
rewrite H5 in H1.
elim (u_conv_0_invar_7 x0 c pl H1).
intros.
elim H7.
intros.
rewrite H8 in H2.
elim (upl_conv_0_occur_in_img x1 b).
intros.
elim (H x x0 c x1 x2 H6 H9).
intros.
split with (umpl_conv_0 x3).
rewrite H10.
exact (u_conv_0_invar_0 d x2 x3 H11).
rewrite H10 in H2.
exact (upl_conv_0_occur x1 x2 H2).
Admitted.

Lemma u_conv_1_ref_ok : forall d : preDTA, preDTA_ref_ok d -> preDTA_ref_ok (udta_conv_1 d).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
elim (u_conv_1_invar_8 d a s H0).
intros.
rewrite H3 in H0.
elim (u_conv_1_invar_5 d x s H0).
intros.
elim H4.
intros.
rewrite H5 in H1.
elim (u_conv_1_invar_7 x0 c pl H1).
intros.
elim H7.
intros.
rewrite H8 in H2.
elim (upl_conv_1_occur_in_img x1 b).
intros.
elim (H x x0 c x1 x2 H6 H9).
intros.
split with (umpl_conv_1 x3).
rewrite H10.
exact (u_conv_1_invar_0 d x2 x3 H11).
rewrite H10 in H2.
exact (upl_conv_1_occur x1 x2 H2).
Admitted.

Lemma u_merge_ref_ok : forall d0 d1 : preDTA, preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> preDTA_ref_ok (u_merge d0 d1).
Proof.
unfold preDTA_ref_ok in |- *.
intros.
elim (adcnv_disj a); intro.
intros.
elim H4; intro.
elim (u_conv_0_ref_ok d0 H a s c pl b (u_merge_0r d0 d1 a s H1 x H5) H2 H3).
intros.
split with x0.
exact (u_merge_0 d0 d1 b x0 H6).
elim (u_conv_1_ref_ok d1 H0 a s c pl b (u_merge_1r d0 d1 a s H1 x H5) H2 H3).
intros.
split with x0.
Admitted.

Lemma upl_conv_compat_0_0 : forall p0 p1 : prec_list, pl_compat p0 p1 -> pl_compat (upl_conv_0 p0) (upl_conv_0 p1).
Proof.
simple induction p0.
simple induction p2.
intros.
unfold pl_compat in |- *.
right.
split.
intro.
inversion H4.
intro.
inversion H4.
intro.
inversion H1.
elim H2.
intros.
inversion H3.
elim H2.
intros.
elim (H4 (refl_equal prec_empty)).
simple induction p1.
intros.
unfold pl_compat in H1.
elim H1; intros.
elim H2.
intros; intros.
inversion H4.
elim H2.
intros.
elim (H3 (refl_equal prec_empty)).
intros.
simpl in |- *.
unfold pl_compat in |- *.
left.
Admitted.

Lemma upl_conv_compat_0_1 : forall p0 p1 : prec_list, pl_compat p0 p1 -> pl_compat (upl_conv_0 p0) (upl_conv_1 p1).
Proof.
simple induction p0.
simple induction p2.
intros.
unfold pl_compat in |- *.
right.
split.
intro.
inversion H4.
intro.
inversion H4.
intro.
inversion H1.
elim H2.
intros.
inversion H3.
elim H2.
intros.
elim (H4 (refl_equal prec_empty)).
simple induction p1.
intros.
unfold pl_compat in H1.
elim H1; intros.
elim H2.
intros; intros.
inversion H4.
elim H2.
intros.
elim (H3 (refl_equal prec_empty)).
intros.
simpl in |- *.
unfold pl_compat in |- *.
left.
Admitted.

Lemma upl_conv_compat_1_0 : forall p0 p1 : prec_list, pl_compat p0 p1 -> pl_compat (upl_conv_1 p0) (upl_conv_0 p1).
Proof.
intros.
Admitted.

Lemma upl_conv_compat_1_1 : forall p0 p1 : prec_list, pl_compat p0 p1 -> pl_compat (upl_conv_1 p0) (upl_conv_1 p1).
Proof.
simple induction p0.
simple induction p2.
intros.
unfold pl_compat in |- *.
right.
split.
intro.
inversion H4.
intro.
inversion H4.
intro.
inversion H1.
elim H2.
intros.
inversion H3.
elim H2.
intros.
elim (H4 (refl_equal prec_empty)).
simple induction p1.
intros.
unfold pl_compat in H1.
elim H1; intros.
elim H2.
intros; intros.
inversion H4.
elim H2.
intros.
elim (H3 (refl_equal prec_empty)).
intros.
simpl in |- *.
unfold pl_compat in |- *.
left.
Admitted.

Lemma umpl_conv_0_compat : forall s0 s1 : state, mpl_compat s0 s1 -> mpl_compat (umpl_conv_0 s0) (umpl_conv_0 s1).
Proof.
unfold mpl_compat in |- *.
intros.
elim (u_conv_0_invar_7 s0 c p0).
elim (u_conv_0_invar_7 s1 c p1).
intros.
elim H2.
elim H3.
intros.
rewrite H4.
rewrite H6.
apply (upl_conv_compat_0_0 x0 x).
exact (H c x0 x H5 H7).
assumption.
Admitted.

Lemma umpl_conv_1_compat : forall s0 s1 : state, mpl_compat s0 s1 -> mpl_compat (umpl_conv_1 s0) (umpl_conv_1 s1).
Proof.
unfold mpl_compat in |- *.
intros.
elim (u_conv_1_invar_7 s0 c p0).
elim (u_conv_1_invar_7 s1 c p1).
intro.
intros.
elim H2.
elim H3.
intros.
rewrite H4.
rewrite H6.
apply (upl_conv_compat_1_1 x0 x).
exact (H c x0 x H5 H7).
assumption.
Admitted.

Lemma udta_conv_0_compat : forall d : preDTA, dta_correct d -> dta_correct (udta_conv_0 d).
Proof.
unfold dta_correct in |- *.
intros.
elim (u_conv_0_invar_8 d a0 s0).
elim (u_conv_0_invar_8 d a1 s1).
intros.
rewrite H2 in H1.
rewrite H3 in H0.
elim (u_conv_0_invar_5 d x s1 H1).
elim (u_conv_0_invar_5 d x0 s0 H0).
intros.
elim H4.
elim H5.
intros.
rewrite H6.
rewrite H8.
exact (umpl_conv_0_compat x1 x2 (H x1 x2 x0 x H9 H7)).
assumption.
Admitted.

Lemma udta_conv_1_compat : forall d : preDTA, dta_correct d -> dta_correct (udta_conv_1 d).
Proof.
unfold dta_correct in |- *.
intros.
elim (u_conv_1_invar_8 d a0 s0).
elim (u_conv_1_invar_8 d a1 s1).
intros.
rewrite H2 in H1.
rewrite H3 in H0.
elim (u_conv_1_invar_5 d x s1 H1).
elim (u_conv_1_invar_5 d x0 s0 H0).
intros.
elim H4.
elim H5.
intros.
rewrite H6.
rewrite H8.
exact (umpl_conv_1_compat x1 x2 (H x1 x2 x0 x H9 H7)).
assumption.
Admitted.

Lemma udta_conv_0_1_compat : forall d0 d1 : preDTA, dta_compat d0 d1 -> dta_compat (udta_conv_0 d0) (udta_conv_1 d1).
Proof.
unfold dta_compat in |- *.
intros.
elim (u_conv_0_invar_8 d0 a0 s0 H0).
elim (u_conv_1_invar_8 d1 a1 s1 H1).
intros.
intros.
rewrite H3 in H0.
rewrite H2 in H1.
elim (u_conv_0_invar_5 d0 x0 s0 H0).
elim (u_conv_1_invar_5 d1 x s1 H1).
intros.
elim H4.
elim H5.
intros.
rewrite H6.
rewrite H8.
Admitted.

Lemma insert_ostate_9 : forall (d0 d1 : preDTA) (a0 a1 a : ad) (s0' s1' : state) (t : term), preDTA_ref_ok d0 -> preDTA_ref_ok d1 -> dta_compat d0 d1 -> MapGet state (u_merge d0 d1) (uad_conv_0 a0) = Some s0' -> MapGet state (u_merge d0 d1) (uad_conv_1 a1) = Some s1' -> a = new_preDTA_ad (u_merge d0 d1) -> (reconnaissance d0 a0 t \/ reconnaissance d1 a1 t <-> reconnaissance (insert_ostate (u_merge d0 d1) a (Some (union_mpl s0' s1'))) a t).
Proof.
intros.
elim (u_conv_0_invar_5 d0 a0 s0' (u_merge_0r d0 d1 (uad_conv_0 a0) s0' H2 a0 (refl_equal _))).
elim (u_conv_1_invar_5 d1 a1 s1' (u_merge_1r d0 d1 (uad_conv_1 a1) s1' H3 a1 (refl_equal _))).
intros.
elim H5.
elim H6.
intros.
cut (mpl_compat s0' s1').
intro.
exact (insert_ostate_8 d0 d1 a0 a1 a x0 x s0' s1' t H11 H8 H10 H2 H3 (u_merge_ref_ok d0 d1 H H0) H4).
apply (udta_conv_0_1_compat d0 d1 H1 s0' s1' (uad_conv_0 a0) (uad_conv_1 a1)).
exact (u_merge_0r d0 d1 (uad_conv_0 a0) s0' H2 a0 (refl_equal _)).
Admitted.

Lemma union_semantics_0 : forall (d0 d1 : DTA) (t : term), DTA_main_state_correct d0 -> DTA_main_state_correct d1 -> DTA_ref_ok d0 -> DTA_ref_ok d1 -> DTA_compat d0 d1 -> (reconnait d0 t \/ reconnait d1 t <-> reconnait (union d0 d1) t).
Proof.
unfold union in |- *.
simple induction d0.
simple induction d1.
intros.
unfold union_1 in |- *.
unfold union_0 in |- *.
elim H.
elim H0.
intros.
unfold DTA_ref_ok in H1.
unfold DTA_ref_ok in H2.
unfold DTA_compat in H3.
unfold insert_main_ostate in |- *.
unfold insert_main_ostate_0 in |- *.
unfold reconnait in |- *.
rewrite (u_merge_0 p p0 (uad_conv_0 a) (umpl_conv_0 x0) (u_conv_0_invar_0 p a x0 H5)).
rewrite (u_merge_1 p p0 (uad_conv_1 a0) (umpl_conv_1 x) (u_conv_1_invar_0 p0 a0 x H4)).
unfold union_opt_state in |- *.
apply (insert_ostate_9 p p0 a a0 (new_preDTA_ad (u_merge p p0)) (umpl_conv_0 x0) (umpl_conv_1 x) t H1 H2 H3).
exact (u_merge_0 p p0 (uad_conv_0 a) (umpl_conv_0 x0) (u_conv_0_invar_0 p a x0 H5)).
exact (u_merge_1 p p0 (uad_conv_1 a0) (umpl_conv_1 x) (u_conv_1_invar_0 p0 a0 x H4)).
Admitted.

Lemma union_semantics : forall (d0 d1 : DTA) (sigma : signature) (t : term), DTA_main_state_correct d0 -> DTA_main_state_correct d1 -> DTA_ref_ok d0 -> DTA_ref_ok d1 -> dta_correct_wrt_sign d0 sigma -> dta_correct_wrt_sign d1 sigma -> (reconnait d0 t \/ reconnait d1 t <-> reconnait (union d0 d1) t).
Proof.
intros.
apply (union_semantics_0 d0 d1 t H H0 H1 H2).
Admitted.

Lemma umpl_conv_0_1_compat : forall s0 s1 : state, mpl_compat s0 s1 -> mpl_compat (umpl_conv_0 s0) (umpl_conv_1 s1).
Proof.
unfold mpl_compat in |- *.
intros.
elim (u_conv_0_invar_7 s0 c p0 H0).
elim (u_conv_1_invar_7 s1 c p1).
intros.
elim H2.
elim H3.
intros.
rewrite H4.
rewrite H6.
apply (upl_conv_compat_0_1 x0 x).
exact (H c x0 x H5 H7).
assumption.
