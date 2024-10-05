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

Lemma u_conv1_2 : forall d : preDTA, u_conv_lr_1 d prec_empty tnil (rec_empty d).
Proof.
intros.
unfold u_conv_lr_1 in |- *.
simpl in |- *.
Admitted.

Lemma u_conv1_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), u_conv_rec_1 d a hd r -> forall l : liste_reconnait d la tl, u_conv_lr_1 d la tl l -> u_conv_lr_1 d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
intros.
unfold u_conv_lr_1 in |- *.
unfold u_conv_lr_1 in H0.
unfold u_conv_rec_1 in H.
simpl in |- *.
Admitted.

Lemma u_conv1_4 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)), u_conv_lr_1 d ls (tcons hd tl) l -> u_conv_lr_1 d (prec_cons a la ls) (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
intros.
unfold u_conv_lr_1 in |- *.
unfold u_conv_lr_1 in H.
simpl in |- *.
Admitted.

Lemma u_conv1_5 : forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t), u_conv_rec_1 p a t r.
Proof.
Admitted.

Lemma u_conv1 : forall (p : preDTA) (a : ad) (t : term), reconnaissance p a t -> reconnaissance (udta_conv_1 p) (uad_conv_1 a) t.
Proof.
intros.
Admitted.

Lemma u_conv1_0r : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), u_conv_str_1_r d ladj t s -> u_conv_rec_1_r d a t (rec_dta d a t ladj e s).
Proof.
intros.
unfold u_conv_str_1_r in H.
unfold u_conv_rec_1_r in |- *.
intros.
rewrite H0 in e.
rewrite H1 in e.
elim (u_conv_1_invar_5 p a0 ladj e).
intros.
elim H2.
intros.
apply (rec_dta p a0 t x H4).
apply (H p x).
exact H0.
Admitted.

Lemma u_conv1_1r : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), u_conv_lr_1_r d l tl l0 -> u_conv_str_1_r d s (app c tl) (rec_st d s c tl l e l0).
Proof.
intros.
unfold u_conv_lr_1_r in H.
unfold u_conv_str_1_r in |- *.
intros.
rewrite H1 in e.
elim (u_conv_1_invar_7 s0 c l e).
intros.
elim H2.
intros.
apply (rec_st p s0 c tl x H4).
Admitted.

Lemma u_conv1_2r : forall d : preDTA, u_conv_lr_1_r d prec_empty tnil (rec_empty d).
Proof.
intros.
unfold u_conv_lr_1_r in |- *.
intros.
cut (pl = prec_empty).
intros.
rewrite H1.
exact (rec_empty p).
cut (upl_conv_1 prec_empty = prec_empty).
intros.
rewrite <- H1 in H0.
symmetry in |- *.
exact (upl_conv_1_inj prec_empty pl H0).
simpl in |- *.
Admitted.

Lemma u_conv1_3r : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), u_conv_rec_1_r d a hd r -> forall l : liste_reconnait d la tl, u_conv_lr_1_r d la tl l -> u_conv_lr_1_r d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
intros.
unfold u_conv_lr_1_r in |- *.
unfold u_conv_rec_1_r in H.
unfold u_conv_lr_1_r in H0.
intros.
cut (upl_conv_1 pl = prec_cons a la ls).
intro.
cut (exists a0 : ad, (exists la0 : prec_list, (exists ls0 : prec_list, pl = prec_cons a0 la0 ls0 /\ a = uad_conv_1 a0 /\ la = upl_conv_1 la0 /\ ls = upl_conv_1 ls0))).
intro.
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
rewrite H8.
apply (rec_consi p x x0 x1 hd tl).
apply (H p x).
exact H1.
trivial.
exact (H0 p x0 H1 H12).
exact (upl_conv_1_img_0 pl a la ls H3).
symmetry in |- *.
Admitted.

Lemma u_conv1_4r : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)), u_conv_lr_1_r d ls (tcons hd tl) l -> u_conv_lr_1_r d (prec_cons a la ls) (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
intros.
unfold u_conv_lr_1_r in H.
unfold u_conv_lr_1_r in |- *.
intros.
cut (upl_conv_1 pl = prec_cons a la ls).
cut (exists a0 : ad, (exists la0 : prec_list, (exists ls0 : prec_list, pl = prec_cons a0 la0 ls0 /\ a = uad_conv_1 a0 /\ la = upl_conv_1 la0 /\ ls = upl_conv_1 ls0))).
intros.
elim H2.
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
rewrite H7.
exact (rec_consn p x x0 x1 hd tl (H p x1 H0 H12)).
cut (upl_conv_1 pl = prec_cons a la ls).
intro.
exact (upl_conv_1_img_0 pl a la ls H2).
symmetry in |- *.
trivial.
symmetry in |- *.
Admitted.

Lemma u_conv1_r : forall (p : preDTA) (a : ad) (t : term), reconnaissance (udta_conv_1 p) (uad_conv_1 a) t -> reconnaissance p a t.
Proof.
intros.
apply (u_conv1_5r (udta_conv_1 p) (uad_conv_1 a) t H p a).
trivial.
Admitted.

Lemma u_conv_disj : forall (p0 p1 : preDTA) (a0 a1 : ad) (s0 s1 : state), MapGet state (udta_conv_0 p0) a0 = Some s0 -> MapGet state (udta_conv_1 p1) a1 = Some s1 -> a0 <> a1.
Proof.
intros.
intro.
cut (exists a2 : _, a0 = uad_conv_0 a2).
cut (exists a3 : _, a1 = uad_conv_1 a3).
intros.
elim H2.
elim H3.
intros.
rewrite <- H1 in H5.
rewrite H4 in H5.
exact (adcnv_ok x x0 H5).
exact (u_conv_1_invar_8 p1 a1 s1 H0).
Admitted.

Lemma u_merge_0 : forall (p0 p1 : preDTA) (a : ad) (s : state), MapGet state (udta_conv_0 p0) a = Some s -> MapGet state (u_merge p0 p1) a = Some s.
Proof.
intros.
unfold u_merge in |- *.
cut (eqm state (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1))) (fun a0 : ad => match MapGet state (udta_conv_1 p1) a0 with | None => MapGet state (udta_conv_0 p0) a0 | Some y' => Some y' end)).
intros.
unfold eqm in H0.
cut (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)) a = match MapGet state (udta_conv_1 p1) a with | None => MapGet state (udta_conv_0 p0) a | Some y' => Some y' end).
intros.
rewrite H1.
cut (MapGet state (udta_conv_1 p1) a = None \/ (exists y : state, MapGet state (udta_conv_1 p1) a = Some y)).
intro.
elim H2; intros.
rewrite H3.
rewrite H.
trivial.
elim H3.
intros.
rewrite H4.
elim (u_conv_disj p0 p1 a a s x H H4 (refl_equal a)).
elim (MapGet state (udta_conv_1 p1) a).
Focus 2.
left.
trivial.
right.
split with a0.
trivial.
exact (H0 a).
Admitted.

Lemma u_merge_1 : forall (p0 p1 : preDTA) (a : ad) (s : state), MapGet state (udta_conv_1 p1) a = Some s -> MapGet state (u_merge p0 p1) a = Some s.
Proof.
intros.
unfold u_merge in |- *.
cut (eqm state (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1))) (fun a0 : ad => match MapGet state (udta_conv_1 p1) a0 with | None => MapGet state (udta_conv_0 p0) a0 | Some y' => Some y' end)).
intros.
unfold eqm in H0.
cut (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)) a = match MapGet state (udta_conv_1 p1) a with | None => MapGet state (udta_conv_0 p0) a | Some y' => Some y' end).
intros.
rewrite H1.
rewrite H.
trivial.
exact (H0 a).
Admitted.

Lemma u_merge_0r : forall (p0 p1 : preDTA) (a : ad) (s : state), MapGet state (u_merge p0 p1) a = Some s -> forall b : ad, a = uad_conv_0 b -> MapGet state (udta_conv_0 p0) a = Some s.
Proof.
intros.
cut (eqm state (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1))) (fun a0 : ad => match MapGet state (udta_conv_1 p1) a0 with | None => MapGet state (udta_conv_0 p0) a0 | Some y' => Some y' end)).
intro.
unfold eqm in H1.
unfold u_merge in H.
rewrite H0.
rewrite H0 in H.
cut (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)) (uad_conv_0 b) = match MapGet state (udta_conv_1 p1) (uad_conv_0 b) with | None => MapGet state (udta_conv_0 p0) (uad_conv_0 b) | Some y' => Some y' end).
intro.
rewrite H2 in H.
cut (MapGet state (udta_conv_1 p1) (uad_conv_0 b) = None \/ (exists s : state, MapGet state (udta_conv_1 p1) (uad_conv_0 b) = Some s)).
intros.
elim H3; intros.
rewrite H4 in H.
assumption.
elim H4.
intros.
elim (u_conv_1_invar_8 p1 (uad_conv_0 b) x).
intros.
elim (adcnv_ok b x0 H6).
assumption.
generalize (MapGet state (udta_conv_1 p1) (uad_conv_0 b)).
simple induction o.
Focus 2.
left.
trivial.
intro.
right.
split with a0.
trivial.
exact (H1 (uad_conv_0 b)).
Admitted.

Lemma u_merge_1r : forall (p0 p1 : preDTA) (a : ad) (s : state), MapGet state (u_merge p0 p1) a = Some s -> forall b : ad, a = uad_conv_1 b -> MapGet state (udta_conv_1 p1) a = Some s.
Proof.
intros.
cut (eqm state (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1))) (fun a0 : ad => match MapGet state (udta_conv_1 p1) a0 with | None => MapGet state (udta_conv_0 p0) a0 | Some y' => Some y' end)).
intro.
unfold eqm in H1.
unfold u_merge in H.
rewrite H0.
rewrite H0 in H.
cut (MapGet state (MapMerge state (udta_conv_0 p0) (udta_conv_1 p1)) (uad_conv_1 b) = match MapGet state (udta_conv_1 p1) (uad_conv_1 b) with | None => MapGet state (udta_conv_0 p0) (uad_conv_1 b) | Some y' => Some y' end).
intros.
rewrite H2 in H.
cut (MapGet state (udta_conv_1 p1) (uad_conv_1 b) = None \/ (exists s : _, MapGet state (udta_conv_1 p1) (uad_conv_1 b) = Some s)).
intro.
elim H3; intros.
rewrite H4 in H.
elim (u_conv_0_invar_8 p0 (uad_conv_1 b) s H).
intros.
elim (adcnv_ok x b (sym_eq H5)).
elim H4.
intros.
rewrite H5 in H.
inversion H.
rewrite <- H7.
exact H5.
generalize (MapGet state (udta_conv_1 p1) (uad_conv_1 b)).
simple induction o.
Focus 2.
left.
trivial.
intros.
right.
split with a0.
trivial.
exact (H1 (uad_conv_1 b)).
Admitted.

Lemma u_merge_2_0 : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), u_merge_inv_0_st d ladj t s -> u_merge_inv_0_dta d a t (rec_dta d a t ladj e s).
Proof.
intros.
unfold u_merge_inv_0_st in H.
unfold u_merge_inv_0_dta in |- *.
intro.
apply (rec_dta (u_merge d p1) (uad_conv_0 a) t (umpl_conv_0 ladj)).
apply (u_merge_0 d p1 (uad_conv_0 a) (umpl_conv_0 ladj)).
exact (u_conv_0_invar_0 d a ladj e).
Admitted.

Lemma u_merge_2_1 : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), u_merge_inv_0_lst d l tl l0 -> u_merge_inv_0_st d s (app c tl) (rec_st d s c tl l e l0).
Proof.
intros.
unfold u_merge_inv_0_lst in H.
unfold u_merge_inv_0_st in |- *.
intros.
apply (rec_st (u_merge d p1) (umpl_conv_0 s) c tl (upl_conv_0 l)).
apply (u_conv_0_invar_1 s c l).
assumption.
Admitted.

Lemma u_merge_2_2 : forall d : preDTA, u_merge_inv_0_lst d prec_empty tnil (rec_empty d).
Proof.
unfold u_merge_inv_0_lst in |- *.
simpl in |- *.
intros.
Admitted.

Lemma u_merge_2_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), u_merge_inv_0_dta d a hd r -> forall l : liste_reconnait d la tl, u_merge_inv_0_lst d la tl l -> u_merge_inv_0_lst d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
intros.
unfold u_merge_inv_0_lst in H0.
unfold u_merge_inv_0_lst in |- *.
unfold u_merge_inv_0_dta in |- *.
simpl in |- *.
unfold u_merge_inv_0_dta in H.
intros.
apply (rec_consi (u_merge d p1) (uad_conv_0 a) (upl_conv_0 la) (upl_conv_0 ls) hd tl).
exact (H p1).
Admitted.

Lemma u_conv1_5r : forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t), u_conv_rec_1_r p a t r.
Proof.
exact (mreconnaissance_ind u_conv_rec_1_r u_conv_str_1_r u_conv_lr_1_r u_conv1_0r u_conv1_1r u_conv1_2r u_conv1_3r u_conv1_4r).
