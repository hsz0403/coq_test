Require Import Bool.
Require Import Arith.
Require Import NArith.
Require Import Ndec.
Require Import ZArith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import lattice_fixpoint.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import pl_path.
Fixpoint pl_non_empty (m : Map bool) (p : prec_list) {struct p} : bool := match p with | prec_empty => true | prec_cons a la ls => match ls with | prec_empty => match MapGet bool m a with | Some b => b && pl_non_empty m la | None => false end | prec_cons _ _ _ => match MapGet bool m a with | Some b => pl_non_empty m ls || b && pl_non_empty m la | None => pl_non_empty m ls end end end.
Fixpoint st_non_empty (m : Map bool) (s : state) {struct s} : bool := match s with | M0 => false | M1 _ p => pl_non_empty m p | M2 a b => st_non_empty m a || st_non_empty m b end.
Fixpoint dta_app_ne_aux (d : preDTA) (m r : Map bool) {struct r} : Map bool := match d, r with | M0, _ => M0 bool | M1 a s, M0 => M0 bool | M1 a s, M1 a' b => if N.eqb a a' then M1 bool a (b || st_non_empty m s) else M0 bool | M1 a s, M2 _ _ => M0 bool | M2 d0 d1, M0 => M0 bool | M2 d0 d1, M1 _ _ => M0 bool | M2 d0 d1, M2 r0 r1 => M2 bool (dta_app_ne_aux d0 m r0) (dta_app_ne_aux d1 m r1) end.
Definition dta_app_ne (d : preDTA) (m : Map bool) : Map bool := dta_app_ne_aux d m m.
Definition dta_non_empty_states (d : preDTA) : Map bool := power (Map bool) (dta_app_ne d) (map_mini state d) (S (MapCard state d)).
Definition dta_states_non_empty (d : DTA) : Map bool := match d with | dta p a => dta_non_empty_states p end.
Definition dta_non_empty_states_lazy (d : preDTA) : Map bool := lazy_power bool eqm_bool (dta_app_ne d) (map_mini state d) (S (MapCard state d)).
Definition dta_states_non_empty_lazy (d : DTA) : Map bool := match d with | dta p a => dta_non_empty_states_lazy p end.
Inductive pl_path_true : pl_path -> Map bool -> Prop := | plp_true_nil : forall m : Map bool, pl_path_true pl_path_nil m | plp_true_cons : forall (m : Map bool) (a : ad) (pl : pl_path), pl_path_true pl m -> MapGet bool m a = Some true -> pl_path_true (pl_path_cons a pl) m.
Definition pl_non_empty_path_true_def_0 (pl : pl_path) (p : prec_list) : Prop := forall m : Map bool, pl_path_incl pl p -> pl_path_true pl m -> pl_non_empty m p = true.
Definition dt_non_empty_def_0 (d : preDTA) (a : ad) (t : term) (pr : reconnaissance d a t) := forall n : nat, term_high t <= n -> MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true.
Definition dt_non_empty_def_1 (d : preDTA) (s : state) (t : term) (pr : state_reconnait d s t) := forall n : nat, term_high t <= S n -> st_non_empty (power (Map bool) (dta_app_ne d) (map_mini state d) n) s = true.
Definition dt_non_empty_def_2 (d : preDTA) (p : prec_list) (t : term_list) (pr : liste_reconnait d p t) := forall n : nat, term_high_0 t <= n -> pl_non_empty (power (Map bool) (dta_app_ne d) (map_mini state d) n) p = true.
Definition dt_non_empty_r_def_0 (n : nat) : Prop := forall (d : preDTA) (a : ad), MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true -> exists t : term, reconnaissance d a t.

Lemma dta_states_non_empty_lazy_eg_dta_states_non_empty : forall d : DTA, dta_states_non_empty_lazy d = dta_states_non_empty d.
Proof.
simple induction d.
simpl in |- *.
intros.
unfold dta_non_empty_states_lazy, dta_non_empty_states in |- *.
apply (lazy_power_eg_power bool eqm_bool (dta_app_ne p) (map_mini state p) (S (MapCard state p))).
split.
exact (eqm_bool_equal a0 b).
intros.
rewrite H.
Admitted.

Lemma dta_app_ne_aux_def_ok : forall (d : preDTA) (m : Map bool), def_ok_app bool (ensemble_base state d) (dta_app_ne_aux d m).
Proof.
simple induction d.
intros.
unfold def_ok_app in |- *.
intros.
induction x as [| a a0| x1 Hrecx1 x0 Hrecx0].
simpl in |- *.
unfold ensemble_base in |- *.
exact I.
unfold ensemble_base in |- *.
simpl in |- *.
exact I.
simpl in |- *.
unfold ensemble_base in |- *.
simpl in |- *.
exact I.
intros.
unfold def_ok_app in |- *.
intros.
unfold ensemble_base in |- *.
unfold ensemble_base in H.
induction x as [| a1 a2| x1 Hrecx1 x0 Hrecx0].
simpl in H.
inversion H.
simpl in H.
simpl in |- *.
rewrite H.
rewrite (Neqb_correct a1).
simpl in |- *.
reflexivity.
simpl in H.
inversion H.
intros.
unfold def_ok_app in |- *.
unfold ensemble_base in |- *.
intros.
induction x as [| a a0| x1 Hrecx1 x0 Hrecx0].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in |- *.
split.
unfold def_ok_app in H.
unfold ensemble_base in H.
simpl in H1.
elim H1.
intros.
exact (H m1 x1 H2).
unfold def_ok_app in H0.
unfold ensemble_base in H0.
elim H1.
intros.
Admitted.

Lemma dta_app_ne_def_ok : forall d : preDTA, def_ok_app bool (ensemble_base state d) (dta_app_ne d).
Proof.
intros.
unfold dta_app_ne in |- *.
unfold def_ok_app in |- *.
intros.
Admitted.

Lemma dta_app_ne_inc_1 : forall (s : state) (m0 m1 : Map bool), lem m0 m1 -> leb (st_non_empty m0 s) (st_non_empty m1 s).
Proof.
simple induction s.
intros.
simpl in |- *.
exact I.
intros.
simpl in |- *.
exact (dta_app_ne_inc_0 a0 m0 m1 H).
intros.
simpl in |- *.
Admitted.

Lemma dta_app_ne_inc_2 : forall (d : preDTA) (m0 m1 m : Map bool), lem m0 m1 -> lem (dta_app_ne_aux d m0 m) (dta_app_ne_aux d m1 m).
Proof.
simple induction d.
simple induction m.
intros.
simpl in |- *.
exact I.
intros.
simpl in |- *.
exact I.
intros.
simpl in |- *.
exact I.
simple induction m.
intros.
simpl in |- *.
exact I.
simpl in |- *.
intros.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H0.
simpl in |- *.
rewrite (Neqb_correct a).
exact (orb_inc_r _ _ _ (dta_app_ne_inc_1 a0 m0 m1 H)).
exact I.
intros.
simpl in |- *.
exact I.
simple induction m3.
intros.
simpl in |- *.
exact I.
intros.
simpl in |- *.
exact I.
intros.
simpl in |- *.
split.
exact (H _ _ _ H3).
Admitted.

Lemma dta_app_ne_inc_3 : forall (m0 m1 m : Map bool) (d : preDTA), lem m0 m1 -> lem (dta_app_ne_aux d m m0) (dta_app_ne_aux d m m1).
Proof.
simple induction m0.
simple induction m1; intros.
induction d as [| a a0| d1 Hrecd1 d0 Hrecd0]; simpl in |- *; exact I.
inversion H.
inversion H1.
simple induction m1; intros.
inversion H.
induction d as [| a3 a4| d1 Hrecd1 d0 Hrecd0]; simpl in |- *.
exact I.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intro; rewrite H0 in H.
rewrite (Neqb_complete _ _ H0).
elim (bool_is_true_or_false (N.eqb a3 a1)); intro; rewrite H1.
simpl in |- *.
rewrite (Neqb_correct a3).
exact (orb_inc_l _ _ _ H).
exact I.
elim H.
exact I.
inversion H1.
simple induction m2; intros.
inversion H1.
inversion H1.
elim H3; intros.
induction d as [| a a0| d1 Hrecd1 d0 Hrecd0]; simpl in |- *.
exact I.
exact I.
split.
exact (H _ _ _ H4).
Admitted.

Lemma dta_app_ne_inc : forall d : preDTA, increasing_app bool lem (dta_app_ne d).
Proof.
intros.
unfold increasing_app in |- *.
unfold dta_app_ne in |- *.
intros.
Admitted.

Lemma pl_non_empty_path_true_0 : pl_non_empty_path_true_def_0 pl_path_nil prec_empty.
Proof.
unfold pl_non_empty_path_true_def_0 in |- *.
simpl in |- *.
intros.
Admitted.

Lemma pl_non_empty_path_true_1 : forall (plp : pl_path) (a : ad) (la ls : prec_list), pl_path_incl plp la -> pl_non_empty_path_true_def_0 plp la -> pl_non_empty_path_true_def_0 (pl_path_cons a plp) (prec_cons a la ls).
Proof.
unfold pl_non_empty_path_true_def_0 in |- *.
intros.
inversion H2.
simpl in |- *.
rewrite H7.
elim (pl_sum ls); intros.
rewrite H8.
exact (H0 m H H5).
elim H8.
intros.
elim H9.
intros.
elim H10.
intros.
rewrite H11.
rewrite (H0 m H H5).
Admitted.

Lemma pl_non_empty_path_true_2 : forall (plp : pl_path) (a : ad) (la ls : prec_list), pl_path_incl plp ls -> pl_non_empty_path_true_def_0 plp ls -> plp <> pl_path_nil -> pl_non_empty_path_true_def_0 plp (prec_cons a la ls).
Proof.
unfold pl_non_empty_path_true_def_0 in |- *.
intros.
induction plp as [| a0 plp Hrecplp].
elim (H1 (refl_equal _)).
inversion H3.
simpl in |- *.
elim (pl_sum ls); intros.
rewrite H9 in H.
inversion H.
elim H9.
intros.
elim H10.
intros.
elim H11.
intros.
rewrite H12.
rewrite <- H12.
rewrite (H0 m H H3).
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x2 y0.
rewrite y0.
elim (bool_is_true_or_false (x2 && pl_non_empty m la)); intro; rewrite H13; reflexivity.
rewrite y.
Admitted.

Lemma pl_non_empty_path_true : forall (pl : pl_path) (p : prec_list) (m : Map bool), pl_path_incl pl p -> pl_path_true pl m -> pl_non_empty m p = true.
Proof.
intros.
Admitted.

Lemma pl_non_empty_path_true_rev : forall (p : prec_list) (m : Map bool), pl_non_empty m p = true -> exists plp : pl_path, pl_path_incl plp p /\ pl_path_true plp m.
Proof.
simple induction p.
intros.
simpl in H1.
elim (pl_sum p1); intros.
rewrite H2 in H1.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x y0.
rewrite y0 in H1.
elim (bool_is_true_or_false x); intro; rewrite H3 in H1.
elim (bool_is_true_or_false (pl_non_empty m p0)); intros.
elim (H m H4).
intros.
elim H5.
intros.
split with (pl_path_cons a x0).
split.
exact (pl_path_incl_cons x0 a p0 p1 H6).
rewrite H3 in y0.
exact (plp_true_cons m a x0 H7 y0).
rewrite H4 in H1.
inversion H1.
elim (bool_is_true_or_false (pl_non_empty m p0)); intro; rewrite H4 in H1; inversion H1.
rewrite y in H1.
inversion H1.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
rewrite H5 in H1.
rewrite <- H5 in H1.
elim (option_sum bool (MapGet bool m a)); intro y.
elim y.
intros x2 y0.
rewrite y0 in H1.
elim (bool_is_true_or_false (pl_non_empty m p1)); intros.
elim (H0 m H6); intros.
split with x3.
split.
elim H7.
intros.
apply (pl_path_incl_next x3 a p0 p1 H8).
intro.
rewrite H10 in H8.
rewrite H5 in H8.
inversion H8.
exact (H16 (refl_equal _)).
elim H7; intros.
assumption.
rewrite H6 in H1.
elim (bool_is_true_or_false (x2 && pl_non_empty m p0)); intros; rewrite H7 in H1.
elim (bool_is_true_or_false x2); intros; rewrite H8 in H7.
rewrite H8 in y0.
elim (bool_is_true_or_false (pl_non_empty m p0)); intros.
elim (H m H9); intros.
split with (pl_path_cons a x3).
split.
elim H10.
intros.
exact (pl_path_incl_cons x3 a p0 p1 H11).
elim H10.
intros.
exact (plp_true_cons m a x3 H12 y0).
rewrite H9 in H7.
inversion H7.
elim (bool_is_true_or_false (pl_non_empty m p0)); intros; rewrite H9 in H7; inversion H7.
inversion H1.
rewrite y in H1.
elim (H0 _ H1).
intros.
split with x2.
split.
apply (pl_path_incl_next x2 a p0 p1).
elim H6.
intros.
assumption.
intro.
rewrite H7 in H6.
elim H6.
intros.
inversion H8.
rewrite <- H11 in H5.
inversion H5.
exact (H11 (refl_equal _)).
elim H6; intros.
assumption.
intros.
split with pl_path_nil.
split.
exact pl_path_incl_nil.
Admitted.

Lemma st_non_empty_0 : forall (m : Map bool) (s : state) (p : prec_list) (a : ad), MapGet prec_list s a = Some p -> pl_non_empty m p = true -> st_non_empty m s = true.
Proof.
simple induction s; intros.
inversion H.
simpl in |- *.
simpl in H.
elim (bool_is_true_or_false (N.eqb a a1)); intro; rewrite H1 in H; inversion H.
exact H0.
simpl in |- *.
induction a as [| p0].
simpl in H1.
rewrite (H p N0 H1 H2).
simpl in |- *.
reflexivity.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ]; simpl in H1.
rewrite (H0 _ _ H1 H2).
elim (bool_is_true_or_false (st_non_empty m m0)); intro; rewrite H3; reflexivity.
rewrite (H _ _ H1 H2).
reflexivity.
rewrite (H0 _ _ H1 H2).
Admitted.

Lemma st_non_empty_1 : forall (d : preDTA) (m r : Map bool) (a : ad) (l : state), MapGet state d a = Some l -> domain_equal state bool d r -> st_non_empty m l = true -> MapGet bool (dta_app_ne_aux d m r) a = Some true.
Proof.
simple induction d.
intros.
inversion H.
intros.
induction r as [| a2 a3| r1 Hrecr1 r0 Hrecr0].
inversion H0.
simpl in |- *.
simpl in H0.
simpl in H.
rewrite H0.
rewrite (Neqb_correct a2).
simpl in |- *.
rewrite H0 in H.
elim (bool_is_true_or_false (N.eqb a2 a1)); intro; rewrite H2 in H.
inversion H.
rewrite H2.
rewrite H1.
elim (bool_is_true_or_false a3); intros; rewrite H3; reflexivity.
inversion H.
inversion H0.
intros.
induction r as [| a0 a1| r1 Hrecr1 r0 Hrecr0].
inversion H2.
inversion H2.
elim H2; intros.
induction a as [| p].
simpl in |- *.
simpl in H1.
apply (H m1 r1 N0 l H1 H4).
exact H3.
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H1.
elim H2.
intros.
exact (H0 _ _ _ _ H1 H7 H3).
exact (H _ _ _ _ H1 H4 H3).
Admitted.

Lemma dt_non_empty_0 : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), dt_non_empty_def_1 d ladj t s -> dt_non_empty_def_0 d a t (rec_dta d a t ladj e s).
Proof.
unfold dt_non_empty_def_1, dt_non_empty_def_0 in |- *.
intros.
elim (nat_sum n); intros.
rewrite H1 in H0.
induction t as (a0, t).
simpl in H0.
elim (le_Sn_O _ H0).
elim H1.
intros.
rewrite H2.
simpl in |- *.
rewrite H2 in H0.
replace (dta_app_ne d (power (Map bool) (dta_app_ne d) (map_mini state d) x)) with (dta_app_ne_aux d (power (Map bool) (dta_app_ne d) (map_mini state d) x) (power (Map bool) (dta_app_ne d) (map_mini state d) x)).
apply (st_non_empty_1 d (power (Map bool) (dta_app_ne d) (map_mini state d) x) (power (Map bool) (dta_app_ne d) (map_mini state d) x) a ladj e).
exact (power_def_ok bool (ensemble_base state d) (dta_app_ne d) (map_mini state d) x (dta_app_ne_def_ok d) (map_mini_appartient state d)).
exact (H x H0).
Admitted.

Lemma dt_non_empty_1 : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), dt_non_empty_def_2 d l tl l0 -> dt_non_empty_def_1 d s (app c tl) (rec_st d s c tl l e l0).
Proof.
unfold dt_non_empty_def_1 in |- *.
unfold dt_non_empty_def_2 in |- *.
intros.
simpl in H0.
fold term_high_0 in H0.
apply (st_non_empty_0 (power (Map bool) (dta_app_ne d) (map_mini state d) n) s l c e).
Admitted.

Lemma dt_non_empty_2 : forall d : preDTA, dt_non_empty_def_2 d prec_empty tnil (rec_empty d).
Proof.
unfold dt_non_empty_def_2 in |- *.
intros.
simpl in |- *.
Admitted.

Lemma dt_non_empty_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), dt_non_empty_def_0 d a hd r -> forall l : liste_reconnait d la tl, dt_non_empty_def_2 d la tl l -> dt_non_empty_def_2 d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
unfold dt_non_empty_def_0, dt_non_empty_def_2 in |- *.
intros.
simpl in H1.
fold term_high in H1.
elim (pl_non_empty_path_true_rev la (power (Map bool) (dta_app_ne d) (map_mini state d) n) (H0 n (le_trans (term_high_0 tl) _ _ (le_max_r _ _) H1))).
intros.
elim H2.
intros.
apply (pl_non_empty_path_true (pl_path_cons a x) (prec_cons a la ls) (power (Map bool) (dta_app_ne d) (map_mini state d) n)).
exact (pl_path_incl_cons x a la ls H3).
apply (plp_true_cons (power (Map bool) (dta_app_ne d) (map_mini state d) n) a x).
exact H4.
Admitted.

Lemma dt_non_empty_4 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)), dt_non_empty_def_2 d ls (tcons hd tl) l -> dt_non_empty_def_2 d (prec_cons a la ls) (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
unfold dt_non_empty_def_2 in |- *.
intros.
elim (pl_non_empty_path_true_rev _ _ (H n H0)).
intros.
elim H1.
intros.
apply (pl_non_empty_path_true x (prec_cons a la ls) (power (Map bool) (dta_app_ne d) (map_mini state d) n)).
apply (pl_path_incl_next x a la ls H2).
intro.
rewrite H4 in H3.
rewrite H4 in H2.
inversion H2.
rewrite <- H6 in l.
inversion l.
elim (H6 (refl_equal _)).
Admitted.

Lemma dt_non_empty_5 : forall (d : preDTA) (a : ad) (t : term), reconnaissance d a t -> forall n : nat, term_high t <= n -> MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true.
Proof.
Admitted.

Lemma dt_non_empty_6 : forall (p : preDTA) (p0 : prec_list) (t : term_list) (l : liste_reconnait p p0 t), dt_non_empty_def_2 p p0 t l.
Proof.
Admitted.

Lemma dt_non_empty_d : forall (d : preDTA) (a : ad) (t : term), reconnaissance d a t -> exists n : nat, MapGet bool (power (Map bool) (dta_app_ne d) (map_mini state d) n) a = Some true.
Proof.
intros.
split with (term_high t).
Admitted.

Lemma dt_non_empty_7 : forall (d : preDTA) (p : prec_list) (t : term_list), liste_reconnait d p t -> pl_non_empty (power (Map bool) (dta_app_ne d) (map_mini state d) (term_high_0 t)) p = true.
Proof.
intros.
Admitted.

Lemma dta_app_ne_inc_0 : forall (p : prec_list) (m0 m1 : Map bool), lem m0 m1 -> leb (pl_non_empty m0 p) (pl_non_empty m1 p).
Proof.
simple induction p.
intros.
induction p1 as [a0 p1_1 Hrecp1_1 p1_0 Hrecp1_0| ].
elim (option_sum bool (MapGet bool m0 a)); intro y.
elim y.
intros x y0.
elim (option_sum bool (MapGet bool m1 a)); intro y1.
elim y1.
intros x0 y2.
replace (pl_non_empty m0 (prec_cons a p0 (prec_cons a0 p1_1 p1_0))) with (pl_non_empty m0 (prec_cons a0 p1_1 p1_0) || x && pl_non_empty m0 p0).
replace (pl_non_empty m1 (prec_cons a p0 (prec_cons a0 p1_1 p1_0))) with (pl_non_empty m1 (prec_cons a0 p1_1 p1_0) || x0 && pl_non_empty m1 p0).
apply (leb_transitive (pl_non_empty m0 (prec_cons a0 p1_1 p1_0) || x && pl_non_empty m0 p0) (pl_non_empty m0 (prec_cons a0 p1_1 p1_0) || x0 && pl_non_empty m1 p0) (pl_non_empty m1 (prec_cons a0 p1_1 p1_0) || x0 && pl_non_empty m1 p0)).
apply (orb_incr (pl_non_empty m0 (prec_cons a0 p1_1 p1_0)) (pl_non_empty m0 (prec_cons a0 p1_1 p1_0)) (x && pl_non_empty m0 p0) (x0 && pl_non_empty m1 p0)).
exact (leb_reflexive _).
apply (andb_incr x x0 (pl_non_empty m0 p0) (pl_non_empty m1 p0)).
exact (lem_get_leb m0 m1 a x x0 H1 y0 y2).
exact (H _ _ H1).
apply (orb_incr (pl_non_empty m0 (prec_cons a0 p1_1 p1_0)) (pl_non_empty m1 (prec_cons a0 p1_1 p1_0)) (x0 && pl_non_empty m1 p0) (x0 && pl_non_empty m1 p0)).
exact (H0 _ _ H1).
exact (leb_reflexive _).
simpl in |- *.
rewrite y2.
reflexivity.
simpl in |- *.
rewrite y0.
reflexivity.
elim (domain_equal_mapget bool bool m0 m1 a x).
intros.
rewrite H2 in y1.
inversion y1.
exact (lem_domain_equal m0 m1 H1).
exact y0.
elim (option_sum bool (MapGet bool m1 a)); intro y0.
elim y0; intros x y1.
elim (domain_equal_mapget bool bool m1 m0 a x); intros.
rewrite H2 in y.
inversion y.
exact (domain_equal_symmetric bool bool _ _ (lem_domain_equal _ _ H1)).
exact y1.
replace (pl_non_empty m0 (prec_cons a p0 (prec_cons a0 p1_1 p1_0))) with (pl_non_empty m0 (prec_cons a0 p1_1 p1_0)).
replace (pl_non_empty m1 (prec_cons a p0 (prec_cons a0 p1_1 p1_0))) with (pl_non_empty m1 (prec_cons a0 p1_1 p1_0)).
exact (H0 _ _ H1).
simpl in |- *.
rewrite y0.
reflexivity.
simpl in |- *.
rewrite y.
reflexivity.
elim (option_sum bool (MapGet bool m0 a)); intro y.
elim (option_sum bool (MapGet bool m1 a)); intro y0.
elim y; intros x y1.
elim y0; intros x0 y2.
replace (pl_non_empty m0 (prec_cons a p0 prec_empty)) with (x && pl_non_empty m0 p0).
replace (pl_non_empty m1 (prec_cons a p0 prec_empty)) with (x0 && pl_non_empty m1 p0).
apply (leb_transitive (x && pl_non_empty m0 p0) (x0 && pl_non_empty m0 p0) (x0 && pl_non_empty m1 p0)).
apply (andb_inc_l (pl_non_empty m0 p0) x x0).
exact (lem_get_leb _ _ _ _ _ H1 y1 y2).
apply (andb_inc_r x0 (pl_non_empty m0 p0) (pl_non_empty m1 p0)).
exact (H _ _ H1).
simpl in |- *.
rewrite y2.
reflexivity.
simpl in |- *.
rewrite y1.
reflexivity.
elim y.
intros x y1.
elim (domain_equal_mapget bool bool m0 m1 a x).
intros.
rewrite H2 in y0.
inversion y0.
exact (lem_domain_equal _ _ H1).
exact y1.
elim (option_sum bool (MapGet bool m1 a)); intro y0.
elim y0.
intros x y1.
elim (domain_equal_mapget bool bool m1 m0 a x).
intros.
rewrite H2 in y.
inversion y.
exact (domain_equal_symmetric bool bool _ _ (lem_domain_equal _ _ H1)).
exact y1.
simpl in |- *.
rewrite y.
rewrite y0.
exact I.
simpl in |- *.
intros.
exact I.
