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

Lemma upl_conv_1_img_0 : forall (p : prec_list) (a : ad) (la ls : prec_list), upl_conv_1 p = prec_cons a la ls -> exists a0 : ad, (exists la0 : prec_list, (exists ls0 : prec_list, p = prec_cons a0 la0 ls0 /\ a = uad_conv_1 a0 /\ la = upl_conv_1 la0 /\ ls = upl_conv_1 ls0)).
Proof.
intros.
cut (exists a0 : ad, (exists la0 : prec_list, (exists ls0 : prec_list, p = prec_cons a0 la0 ls0))).
intros.
elim H0.
intros.
elim H1.
intros.
elim H2.
intros.
rewrite H3 in H.
split with x.
split with x0.
split with x1.
split.
assumption.
split.
inversion H.
trivial.
split.
inversion H; trivial.
inversion H.
trivial.
Admitted.

Lemma upl_conv_1_img_1 : forall p : prec_list, upl_conv_1 p = prec_empty -> p = prec_empty.
Proof.
simple induction p.
intros.
inversion H1.
intros.
Admitted.

Lemma u_conv_0_invar_0 : forall (d : preDTA) (a : ad) (ladj : state), MapGet state d a = Some ladj -> MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some (umpl_conv_0 ladj).
Proof.
simple induction d.
intros.
simpl in H.
inversion H.
intros.
unfold udta_conv_0 in |- *.
unfold udta_conv_0_aux in |- *.
cut (a = a1).
intro.
rewrite H0.
rewrite H0 in H.
induction a1 as [| p].
simpl in |- *.
simpl in H.
inversion H.
trivial.
simpl in |- *.
simpl in H.
cut (Pos.eqb p p = true).
intro.
rewrite H1 in H.
rewrite H1.
inversion H.
trivial.
exact (aux_Neqb_1_0 p).
intros.
cut (N.eqb a a1 = true).
intro.
exact (Neqb_complete a a1 H0).
cut (N.eqb a a1 = true \/ N.eqb a a1 = false).
intros.
elim H0.
intros.
assumption.
intro.
cut (MapGet state (M1 state a a0) a1 = None).
intro.
rewrite H2 in H.
inversion H.
exact (M1_semantics_2 state a a1 a0 H1).
exact (bool_is_true_or_false (N.eqb a a1)).
intro.
intro.
intro.
intro.
simple induction a.
exact (H N0).
simple induction p.
intros.
simpl in |- *.
simpl in H2.
exact (H0 (Npos p0) ladj H2).
intros.
simpl in |- *.
simpl in H2.
exact (H (Npos p0) ladj H2).
intros.
simpl in H1.
simpl in |- *.
Admitted.

Lemma u_conv_0_invar_1 : forall (s : state) (c : ad) (p : prec_list), MapGet prec_list s c = Some p -> MapGet prec_list (umpl_conv_0 s) c = Some (upl_conv_0 p).
Proof.
simple induction s.
intros.
simpl in H.
inversion H.
intros.
simpl in |- *.
simpl in H.
cut (N.eqb a c = true).
intro.
rewrite H0 in H.
rewrite H0.
inversion H.
trivial.
cut (N.eqb a c = true \/ N.eqb a c = false).
intro.
elim H0; intros.
assumption.
rewrite H1 in H.
inversion H.
exact (bool_is_true_or_false (N.eqb a c)).
intro.
intro.
intro.
intro.
simple induction c.
simpl in |- *.
intros.
exact (H N0 p H1).
simple induction p.
intros.
simpl in H2.
simpl in |- *.
exact (H0 (Npos p0) p1 H2).
intros.
simpl in |- *.
simpl in H2.
exact (H (Npos p0) p1 H2).
intros.
simpl in |- *.
simpl in H1.
Admitted.

Lemma u_conv_0_invar_2 : forall (d : preDTA) (a : ad) (ladj : state), MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some (umpl_conv_0 ladj) -> MapGet state d a = Some ladj.
Proof.
simple induction d.
simple induction a.
intros.
inversion H.
simple induction p.
intros.
inversion H0.
intros.
simpl in H0.
inversion H0.
intros.
inversion H.
simple induction a; intro.
simple induction a1.
simpl in |- *.
intros.
simpl in H.
inversion H.
cut (a0 = ladj).
intros.
rewrite H0.
trivial.
exact (umpl_conv_0_inj a0 ladj H1).
simple induction p.
intros.
simpl in H0.
inversion H0.
intros.
inversion H0.
intros.
inversion H.
intro.
simple induction a1.
intros.
inversion H.
intros.
induction p as [p Hrecp| p Hrecp| ].
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H.
simpl in |- *.
cut (Pos.eqb p p0 = true \/ Pos.eqb p p0 = false).
intro.
elim H0; intros.
rewrite H1.
rewrite H1 in H.
inversion H.
cut (a0 = ladj).
intro.
rewrite H2.
trivial.
exact (umpl_conv_0_inj a0 ladj H3).
rewrite H1.
rewrite H1 in H.
inversion H.
exact (bool_is_true_or_false (Pos.eqb p p0)).
inversion H.
inversion H.
simpl in H.
simpl in |- *.
cut (Pos.eqb (xO p) p0 = true \/ Pos.eqb (xO p) p0 = false).
intro.
elim H0; intros.
rewrite H1.
rewrite H1 in H.
inversion H.
cut (a0 = ladj).
intro.
rewrite H2.
trivial.
exact (umpl_conv_0_inj a0 ladj H3).
rewrite H1 in H.
inversion H.
exact (bool_is_true_or_false (Pos.eqb (xO p) p0)).
simpl in |- *.
simpl in H.
cut (Pos.eqb 1 p0 = true \/ Pos.eqb 1 p0 = false).
intro.
elim H0; intros.
rewrite H1 in H.
rewrite H1.
inversion H.
cut (a0 = ladj).
intros.
rewrite H2.
trivial.
exact (umpl_conv_0_inj a0 ladj H3).
rewrite H1 in H.
inversion H.
exact (bool_is_true_or_false (Pos.eqb 1 p0)).
intros.
induction a as [| p].
simpl in H1.
unfold udta_conv_0 in H.
simpl in |- *.
apply (H N0 ladj).
simpl in |- *.
trivial.
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
unfold udta_conv_0 in H0.
apply (H0 (Npos p) ladj).
simpl in |- *.
simpl in H1.
trivial.
simpl in |- *.
simpl in H1.
unfold udta_conv_0 in H.
exact (H (Npos p) ladj H1).
simpl in |- *.
simpl in H1.
unfold udta_conv_0 in H0.
Admitted.

Lemma u_conv_0_invar_3 : forall (s : state) (c : ad) (p : prec_list), MapGet prec_list (umpl_conv_0 s) c = Some (upl_conv_0 p) -> MapGet prec_list s c = Some p.
Proof.
simple induction s.
intros.
inversion H.
simple induction a.
intro.
simple induction c.
simpl in |- *.
intros.
inversion H.
cut (a0 = p).
intros.
rewrite H0.
trivial.
exact (upl_conv_0_inj a0 p H1).
simpl in |- *.
intros.
inversion H.
intro.
intro.
simple induction c.
simpl in |- *.
intros.
inversion H.
induction p as [p Hrecp| p Hrecp| ].
simple induction p0.
intros.
simpl in H0.
cut (Pos.eqb p p1 = true \/ Pos.eqb p p1 = false).
intros.
elim H1; intros.
simpl in |- *.
rewrite H2.
rewrite H2 in H0.
inversion H0.
cut (a0 = p2).
intro.
rewrite H3.
trivial.
exact (upl_conv_0_inj a0 p2 H4).
simpl in |- *.
rewrite H2.
rewrite H2 in H0.
inversion H0.
exact (bool_is_true_or_false (Pos.eqb p p1)).
intros.
inversion H0.
intros.
inversion H.
simple induction p0.
intros.
inversion H0.
intros.
simpl in H0.
simpl in |- *.
cut (Pos.eqb p p1 = true \/ Pos.eqb p p1 = false).
intros.
elim H1; intros.
rewrite H2 in H0.
rewrite H2.
inversion H0.
cut (a0 = p2).
intro.
rewrite H3.
trivial.
exact (upl_conv_0_inj a0 p2 H4).
rewrite H2.
rewrite H2 in H0.
inversion H0.
exact (bool_is_true_or_false (Pos.eqb p p1)).
intros.
inversion H.
simple induction p.
intros.
inversion H0.
intros.
inversion H0.
intros.
simpl in H.
inversion H.
cut (a0 = p0).
intro.
rewrite H0.
trivial.
exact (upl_conv_0_inj a0 p0 H1).
intro.
intro.
intro.
intro.
simple induction c.
simpl in |- *.
intros.
exact (H N0 p H1).
simple induction p.
intros.
simpl in |- *.
simpl in H2.
exact (H0 (Npos p0) p1 H2).
intros; simpl in |- *.
simpl in H2.
exact (H (Npos p0) p1 H2).
intros; simpl in |- *.
simpl in H1.
Admitted.

Lemma u_conv_0_invar_4 : forall (d : preDTA) (a : ad) (ladj : state), MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some ladj -> exists ladj0 : _, ladj = umpl_conv_0 ladj0.
Proof.
simple induction d.
intros.
induction a as [| p].
simpl in H.
inversion H.
induction p as [p Hrecp| p Hrecp| ]; simpl in H; inversion H.
simple induction a.
intro.
simple induction a1.
intros.
simpl in H.
induction a0 as [| a0 a2| a0_1 Hreca0_1 a0_0 Hreca0_0].
simpl in H.
split with (M0 prec_list).
simpl in |- *.
inversion H.
trivial.
split with (M1 prec_list a0 a2).
inversion H.
trivial.
split with (M2 prec_list a0_1 a0_0).
inversion H.
trivial.
simpl in |- *.
intros.
inversion H.
intro.
intro.
simple induction a1.
simpl in |- *.
intros.
inversion H.
simpl in |- *.
intros.
cut (Pos.eqb p p0 = true \/ Pos.eqb p p0 = false).
intro.
elim H0; intros.
rewrite H1 in H.
inversion H.
split with a0.
trivial.
rewrite H1 in H.
inversion H.
exact (bool_is_true_or_false (Pos.eqb p p0)).
intro.
intro.
intro.
intro.
simple induction a.
simpl in |- *.
intros.
exact (H N0 ladj H1).
simple induction p.
intros.
simpl in H2.
exact (H0 (Npos p0) ladj H2).
intros.
simpl in H2.
exact (H (Npos p0) ladj H2).
simpl in |- *.
intros.
Admitted.

Lemma u_conv_0_invar_5 : forall (d : preDTA) (a : ad) (ladj : state), MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some ladj -> exists ladj0 : _, ladj = umpl_conv_0 ladj0 /\ MapGet state d a = Some ladj0.
Proof.
intros.
cut (exists ladj0 : state, ladj = umpl_conv_0 ladj0).
intros.
elim H0.
intros.
split with x.
split.
assumption.
rewrite H1 in H.
exact (u_conv_0_invar_2 d a x H).
Admitted.

Lemma u_conv_0_invar_6 : forall (s : state) (c : ad) (p : prec_list), MapGet prec_list (umpl_conv_0 s) c = Some p -> exists p0 : prec_list, p = upl_conv_0 p0.
Proof.
simple induction s.
intros.
induction c as [| p0].
inversion H.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; inversion H.
simple induction a.
intro.
simple induction c.
intros.
simpl in H.
inversion H.
split with a0.
trivial.
simpl in |- *.
intros.
inversion H.
simple induction p.
intro.
intro.
simple induction c.
simpl in |- *.
intros.
inversion H0.
simpl in |- *.
simple induction p1.
intros.
simpl in H1.
cut (Pos.eqb p0 p2 = true \/ Pos.eqb p0 p2 = false).
intro.
elim H2.
intros.
rewrite H3 in H1.
inversion H1.
split with a0.
trivial.
intro.
rewrite H3 in H1.
inversion H1.
exact (bool_is_true_or_false (Pos.eqb p0 p2)).
intros.
inversion H1.
intros.
inversion H0.
intro.
intro.
intro.
simple induction c.
intros.
inversion H0.
simple induction p1.
intros.
simpl in H1.
inversion H1.
intros.
simpl in H1.
cut (Pos.eqb p0 p2 = true \/ Pos.eqb p0 p2 = false).
intro.
elim H2; intro.
rewrite H3 in H1.
inversion H1.
split with a0.
trivial.
rewrite H3 in H1.
inversion H1.
exact (bool_is_true_or_false (Pos.eqb p0 p2)).
intros.
inversion H0.
intro.
simple induction c.
intros.
inversion H.
simple induction p0.
intros.
inversion H0.
intros.
inversion H0.
intros.
simpl in H.
inversion H.
split with a0.
trivial.
intro.
intro.
intro.
intro.
simple induction c.
simpl in |- *.
intros.
simpl in H1.
exact (H N0 p H1).
simple induction p.
intros.
simpl in H2.
exact (H0 (Npos p0) p1 H2).
intros.
simpl in H2.
exact (H (Npos p0) p1 H2).
simpl in |- *.
intros.
Admitted.

Lemma u_conv_0_invar_7 : forall (s : state) (c : ad) (p : prec_list), MapGet prec_list (umpl_conv_0 s) c = Some p -> exists p0 : prec_list, p = upl_conv_0 p0 /\ MapGet prec_list s c = Some p0.
Proof.
intros.
elim (u_conv_0_invar_6 s c p H).
intros.
split with x.
intros.
split.
assumption.
rewrite H0 in H.
Admitted.

Lemma u_conv0_0 : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), u_conv_str_0 d ladj t s -> u_conv_rec_0 d a t (rec_dta d a t ladj e s).
Proof.
intros.
unfold u_conv_rec_0 in |- *.
unfold u_conv_str_0 in H.
cut (MapGet state (udta_conv_0 d) (uad_conv_0 a) = Some (umpl_conv_0 ladj)).
intros.
exact (rec_dta (udta_conv_0 d) (uad_conv_0 a) t (umpl_conv_0 ladj) H0 H).
Admitted.

Lemma u_conv0_1 : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), u_conv_lr_0 d l tl l0 -> u_conv_str_0 d s (app c tl) (rec_st d s c tl l e l0).
Proof.
intros.
unfold u_conv_str_0 in |- *.
unfold u_conv_lr_0 in H.
cut (MapGet prec_list (umpl_conv_0 s) c = Some (upl_conv_0 l)).
intros.
exact (rec_st (udta_conv_0 d) (umpl_conv_0 s) c tl (upl_conv_0 l) H0 H).
Admitted.

Lemma u_conv0_2 : forall d : preDTA, u_conv_lr_0 d prec_empty tnil (rec_empty d).
Proof.
intros.
unfold u_conv_lr_0 in |- *.
simpl in |- *.
Admitted.

Lemma u_conv0_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), u_conv_rec_0 d a hd r -> forall l : liste_reconnait d la tl, u_conv_lr_0 d la tl l -> u_conv_lr_0 d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
intros.
unfold u_conv_lr_0 in |- *.
unfold u_conv_rec_0 in H.
unfold u_conv_lr_0 in H0.
simpl in |- *.
Admitted.

Lemma u_conv0_4 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)), u_conv_lr_0 d ls (tcons hd tl) l -> u_conv_lr_0 d (prec_cons a la ls) (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
intros.
unfold u_conv_lr_0 in |- *.
simpl in |- *.
unfold u_conv_lr_0 in H.
Admitted.

Lemma u_conv0_5 : forall (p : preDTA) (a : ad) (t : term) (r : reconnaissance p a t), u_conv_rec_0 p a t r.
Proof.
Admitted.

Lemma u_conv0 : forall (p : preDTA) (a : ad) (t : term), reconnaissance p a t -> reconnaissance (udta_conv_0 p) (uad_conv_0 a) t.
Proof.
intros.
Admitted.

Lemma u_conv0_0r : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), u_conv_str_0_r d ladj t s -> u_conv_rec_0_r d a t (rec_dta d a t ladj e s).
Proof.
intros.
unfold u_conv_str_0_r in H.
unfold u_conv_rec_0_r in |- *.
intros.
rewrite H0 in e.
rewrite H1 in e.
elim (u_conv_0_invar_5 p a0 ladj e).
intros.
elim H2.
intros.
apply (rec_dta p a0 t x H4).
apply (H p x).
exact H0.
Admitted.

Lemma u_conv0_1r : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), u_conv_lr_0_r d l tl l0 -> u_conv_str_0_r d s (app c tl) (rec_st d s c tl l e l0).
Proof.
intros.
unfold u_conv_lr_0_r in H.
unfold u_conv_str_0_r in |- *.
intros.
rewrite H1 in e.
elim (u_conv_0_invar_7 s0 c l e).
intros.
elim H2.
intros.
apply (rec_st p s0 c tl x H4).
Admitted.

Lemma u_conv0_2r : forall d : preDTA, u_conv_lr_0_r d prec_empty tnil (rec_empty d).
Proof.
intros.
unfold u_conv_lr_0_r in |- *.
intros.
cut (pl = prec_empty).
intros.
rewrite H1.
exact (rec_empty p).
cut (upl_conv_0 prec_empty = prec_empty).
intros.
rewrite <- H1 in H0.
symmetry in |- *.
exact (upl_conv_0_inj prec_empty pl H0).
simpl in |- *.
Admitted.

Lemma u_conv_0_invar_8 : forall (p0 : preDTA) (a0 : ad) (s0 : state), MapGet state (udta_conv_0 p0) a0 = Some s0 -> exists a1 : ad, a0 = uad_conv_0 a1.
Proof.
simple induction p0.
intros.
induction a0 as [| p].
simpl in H.
inversion H.
induction p as [p Hrecp| p Hrecp| ]; simpl in H; inversion H.
unfold udta_conv_0 in |- *.
unfold udta_conv_0_aux in |- *.
intros.
induction a as [| p].
split with N0.
unfold uad_conv_0 in |- *.
induction a1 as [| p].
trivial.
simpl in H.
induction p as [p Hrecp| p Hrecp| ]; inversion H.
split with (Npos p).
simpl in |- *.
induction a1 as [| p1].
simpl in H.
inversion H.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
simpl in H.
inversion H.
simpl in H.
cut (Pos.eqb p p1 = true).
intro.
cut (p1 = p).
intro.
rewrite H1.
trivial.
symmetry in |- *.
exact (aux_Neqb_1_1 p p1 H0).
cut (Pos.eqb p p1 = true \/ Pos.eqb p p1 = false).
intro.
elim H0; intros.
assumption.
rewrite H1 in H.
inversion H.
exact (bool_is_true_or_false (Pos.eqb p p1)).
simpl in H.
inversion H.
unfold udta_conv_0 in |- *.
intro.
intro.
intro.
intro.
simple induction a0.
intros.
split with N0.
simpl in |- *.
trivial.
simple induction p.
intros.
inversion H2.
intros.
split with (Npos p1).
simpl in |- *.
trivial.
intros.
inversion H1.
