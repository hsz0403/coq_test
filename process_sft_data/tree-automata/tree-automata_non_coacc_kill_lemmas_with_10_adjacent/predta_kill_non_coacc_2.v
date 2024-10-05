Require Import Bool.
Require Import Arith.
Require Import NArith Ndec.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import refcorrect.
Require Import lattice_fixpoint.
Require Import coacc_test.
Fixpoint non_coacc_kill (d : preDTA) (m : Map bool) {struct m} : preDTA := match d, m with | M0, M0 => M0 state | M1 a s, M1 a' b => if N.eqb a a' && b then M1 state a s else M0 state | M2 x y, M2 z t => M2 state (non_coacc_kill x z) (non_coacc_kill y t) | _, _ => M0 state end.
Definition predta_kill_non_coacc (d : preDTA) (a : ad) : preDTA := non_coacc_kill d (predta_coacc_states d a).
Definition dta_kill_non_coacc (d : DTA) : DTA := match d with | dta p a => dta (predta_kill_non_coacc p a) a end.
Definition predta_kill_non_coacc_lazy (d : preDTA) (a : ad) : preDTA := non_coacc_kill d (predta_coacc_states_0 d a).
Definition dta_kill_non_coacc_lazy (d : DTA) : DTA := match d with | dta p a => dta (predta_kill_non_coacc_lazy p a) a end.
Definition predta_kill_non_coacc_def_0 (d : preDTA) (a0 a1 : ad) : Prop := preDTA_ref_ok d -> coacc d a0 a1 -> coacc (predta_kill_non_coacc d a0) a0 a1.
Definition predta_kill_non_coacc_rec_def_0 (p : preDTA) (a : ad) (t : term) (pr : reconnaissance p a t) := forall (p0 : preDTA) (m : Map bool), p = non_coacc_kill p0 m -> ensemble_base state p0 m -> reconnaissance p0 a t.
Definition predta_kill_non_coacc_rec_def_1 (p : preDTA) (s : state) (t : term) (pr : state_reconnait p s t) := forall (p0 : preDTA) (m : Map bool), p = non_coacc_kill p0 m -> ensemble_base state p0 m -> state_reconnait p0 s t.
Definition predta_kill_non_coacc_rec_def_2 (p : preDTA) (pl : prec_list) (lt : term_list) (pr : liste_reconnait p pl lt) := forall (p0 : preDTA) (m : Map bool), p = non_coacc_kill p0 m -> ensemble_base state p0 m -> liste_reconnait p0 pl lt.
Inductive reconnaissance_co : preDTA -> ad -> ad -> term -> Prop := rec_co_dta : forall (d : preDTA) (a b : ad) (t : term) (ladj : state), MapGet state d a = Some ladj -> state_reconnait_co d ladj b t -> coacc d b a -> reconnaissance_co d a b t with state_reconnait_co : preDTA -> state -> ad -> term -> Prop := rec_co_st : forall (d : preDTA) (s : state) (c b : ad) (tl : term_list) (l : prec_list), MapGet prec_list s c = Some l -> liste_reconnait_co d l b tl -> state_reconnait_co d s b (app c tl) with liste_reconnait_co : preDTA -> prec_list -> ad -> term_list -> Prop := | rec_co_empty : forall (d : preDTA) (b : ad), liste_reconnait_co d prec_empty b tnil | rec_co_consi : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (b : ad) (tl : term_list), reconnaissance_co d a b hd -> liste_reconnait_co d la b tl -> liste_reconnait_co d (prec_cons a la ls) b (tcons hd tl) | rec_co_consn : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (b : ad) (tl : term_list), liste_reconnait_co d ls b (tcons hd tl) -> liste_reconnait_co d (prec_cons a la ls) b (tcons hd tl).
Scheme mreconnaissance_co_ind := Induction for reconnaissance_co Sort Prop with mstrec_co_ind := Induction for state_reconnait_co Sort Prop with mlrec_co_ind := Induction for liste_reconnait_co Sort Prop.
Definition rec_co_def_0 (d : preDTA) (a a1 : ad) (t : term) (pr : reconnaissance_co d a a1 t) := forall a0 : ad, coacc d a0 a1 -> reconnaissance_co d a a0 t.
Definition rec_co_def_1 (d : preDTA) (s : state) (a1 : ad) (t : term) (pr : state_reconnait_co d s a1 t) := forall a0 : ad, coacc d a0 a1 -> state_reconnait_co d s a0 t.
Definition rec_co_def_2 (d : preDTA) (p : prec_list) (a1 : ad) (tl : term_list) (pr : liste_reconnait_co d p a1 tl) := forall a0 : ad, coacc d a0 a1 -> liste_reconnait_co d p a0 tl.
Definition rec_co_def_3 (t : term) : Prop := forall (d : preDTA) (a : ad), preDTA_ref_ok d -> reconnaissance d a t -> reconnaissance_co d a a t.
Definition rec_co_def_4 (d : preDTA) (l : prec_list) (tl : term_list) : Prop := forall a : ad, preDTA_ref_ok d -> liste_reconnait d l tl -> (forall u : term, term_list_occur u tl -> forall (d : preDTA) (a : ad), preDTA_ref_ok d -> reconnaissance d a u -> reconnaissance_co d a a u) -> (forall b : ad, prec_occur l b -> coacc d a b) -> liste_reconnait_co d l a tl.
Definition rec_co_rec_def_0 (d : preDTA) (a a0 : ad) (t : term) (pr : reconnaissance_co d a a0 t) := reconnaissance d a t.
Definition rec_co_rec_def_1 (d : preDTA) (s : state) (a0 : ad) (t : term) (pr : state_reconnait_co d s a0 t) := state_reconnait d s t.
Definition rec_co_rec_def_2 (d : preDTA) (p : prec_list) (a0 : ad) (tl : term_list) (pr : liste_reconnait_co d p a0 tl) := liste_reconnait d p tl.
Definition rec_nonco_kill_def_0 (d : preDTA) (a a0 : ad) (t : term) (pr : reconnaissance_co d a a0 t) := preDTA_ref_ok d -> reconnaissance_co (predta_kill_non_coacc d a0) a a0 t.
Definition rec_nonco_kill_def_1 (d : preDTA) (s : state) (a0 : ad) (t : term) (pr : state_reconnait_co d s a0 t) := preDTA_ref_ok d -> state_reconnait_co (predta_kill_non_coacc d a0) s a0 t.
Definition rec_nonco_kill_def_2 (d : preDTA) (p : prec_list) (a0 : ad) (tl : term_list) (pr : liste_reconnait_co d p a0 tl) := preDTA_ref_ok d -> liste_reconnait_co (predta_kill_non_coacc d a0) p a0 tl.

Lemma kill_non_coacc_lazy_eq_kill_non_coacc : forall d : DTA, dta_kill_non_coacc_lazy d = dta_kill_non_coacc d.
Proof.
intros.
unfold dta_kill_non_coacc_lazy, dta_kill_non_coacc in |- *.
unfold predta_kill_non_coacc_lazy, predta_kill_non_coacc in |- *.
unfold predta_coacc_states, predta_coacc_states_0 in |- *.
induction d as (p, a).
rewrite (lazy_power_eg_power bool eqm_bool (predta_coacc p a) (map_mini state p) (S (MapCard state p))).
reflexivity.
split.
exact (eqm_bool_equal a0 b).
intros.
rewrite H.
Admitted.

Lemma non_coacc_kill_0 : forall (d : preDTA) (a : ad) (s : state) (m : Map bool), ensemble_base state d m -> MapGet state d a = Some s -> MapGet bool m a = Some true -> MapGet state (non_coacc_kill d m) a = Some s.
Proof.
simple induction d; intros.
inversion H0.
induction m as [| a2 a3| m1 Hrecm1 m0 Hrecm0]; simpl in H1.
inversion H1.
simpl in H0.
simpl in |- *.
elim (bool_is_true_or_false (N.eqb a a1)); intros.
rewrite H2 in H0.
elim (bool_is_true_or_false (N.eqb a2 a1)); intros; rewrite H3 in H1; inversion H1.
rewrite (Neqb_complete _ _ H2).
rewrite (Neqb_complete _ _ H3).
rewrite (Neqb_correct a1).
simpl in |- *.
rewrite (Neqb_correct a1).
inversion H0.
reflexivity.
rewrite H2 in H0.
inversion H0.
inversion H.
induction m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H1.
inversion H1.
simpl in |- *.
unfold ensemble_base in H1.
elim H1.
intros.
induction a as [| p]; simpl in |- *; simpl in H2; simpl in H3.
exact (H _ _ _ H4 H2 H3).
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H2; simpl in H3.
exact (H0 _ _ _ H5 H2 H3).
exact (H _ _ _ H4 H2 H3).
Admitted.

Lemma non_coacc_kill_1 : forall (d : preDTA) (a : ad) (s : state) (m : Map bool), ensemble_base state d m -> MapGet state (non_coacc_kill d m) a = Some s -> MapGet state d a = Some s /\ MapGet bool m a = Some true.
Proof.
simple induction d; intros.
induction m as [| a0 a1| m1 Hrecm1 m0 Hrecm0]; inversion H0.
induction m as [| a2 a3| m1 Hrecm1 m0 Hrecm0].
inversion H.
simpl in H.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a2)); intros; rewrite H1 in H0.
elim (bool_is_true_or_false a3); intros; rewrite H2 in H0.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a a1)); intros; rewrite H3 in H0; inversion H0.
rewrite (Neqb_complete _ _ H1).
simpl in |- *.
rewrite <- (Neqb_complete _ _ H1).
rewrite <- (Neqb_complete _ _ H3).
rewrite H2.
rewrite (Neqb_correct a).
split; reflexivity.
simpl in H0.
inversion H0.
simpl in H0.
inversion H0.
inversion H.
induction m1 as [| a0 a1| m1_1 Hrecm1_1 m1_0 Hrecm1_0].
inversion H1.
inversion H1.
unfold ensemble_base in H1.
elim H1.
intros.
induction a as [| p]; simpl in |- *; simpl in H2.
exact (H _ _ _ H3 H2).
induction p as [p Hrecp| p Hrecp| ]; simpl in |- *; simpl in H2.
exact (H0 _ _ _ H4 H2).
exact (H _ _ _ H3 H2).
Admitted.

Lemma predta_kill_non_coacc_0 : forall (d : preDTA) (a a0 : ad) (s : state), preDTA_ref_ok d -> (MapGet state d a0 = Some s /\ coacc d a a0 <-> MapGet state (predta_kill_non_coacc d a) a0 = Some s).
Proof.
intros.
split.
intros.
intros.
elim (predta_coacc_fix d a a0).
intros.
intros.
elim H0.
intros.
apply (fun p : ensemble_base state d (predta_coacc_states d a) => non_coacc_kill_0 d a0 s (predta_coacc_states d a) p H3 (H2 H4)).
unfold predta_coacc_states in |- *.
apply (power_def_ok bool (ensemble_base state d) (predta_coacc d a) (map_mini state d) (S (MapCard state d))).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a x).
exact (map_mini_appartient state d).
exact H.
intros.
unfold predta_kill_non_coacc in H0.
elim (fun p : ensemble_base state d (predta_coacc_states d a) => non_coacc_kill_1 d a0 s (predta_coacc_states d a) p H0).
intros.
split.
exact H1.
elim (predta_coacc_fix d a a0 H).
intros.
exact (H3 H2).
unfold predta_coacc_states in |- *.
apply (power_def_ok bool (ensemble_base state d) (predta_coacc d a) (map_mini state d) (S (MapCard state d))).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a x).
Admitted.

Lemma predta_kill_non_coacc_1 : forall (d : preDTA) (a : ad) (s : state), MapGet state d a = Some s -> predta_kill_non_coacc_def_0 d a a.
Proof.
unfold predta_kill_non_coacc_def_0 in |- *.
intros.
elim (predta_coacc_fix d a a H0).
intros.
apply (coacc_id (predta_kill_non_coacc d a) a s).
unfold predta_kill_non_coacc in |- *.
apply (non_coacc_kill_0 d a s (predta_coacc_states d a)).
unfold predta_coacc_states in |- *.
apply (power_def_ok bool (ensemble_base state d) (predta_coacc d a) (map_mini state d) (S (MapCard state d))).
unfold def_ok_app in |- *.
intros.
exact (predta_coacc_def_ok d a x).
exact (map_mini_appartient state d).
exact H.
Admitted.

Lemma predta_kill_non_coacc_3 : forall (d : preDTA) (a0 a1 : ad), preDTA_ref_ok d -> coacc d a0 a1 -> coacc (predta_kill_non_coacc d a0) a0 a1.
Proof.
intros.
Admitted.

Lemma predta_kill_non_coacc_rec_0 : forall (d : preDTA) (a : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait d ladj t), predta_kill_non_coacc_rec_def_1 d ladj t s -> predta_kill_non_coacc_rec_def_0 d a t (rec_dta d a t ladj e s).
Proof.
unfold predta_kill_non_coacc_rec_def_1, predta_kill_non_coacc_rec_def_0 in |- *.
intros.
rewrite H0 in e.
apply (rec_dta p0 a t ladj).
elim (non_coacc_kill_1 _ _ _ _ H1 e).
intros.
exact H2.
Admitted.

Lemma predta_kill_non_coacc_rec_1 : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait d l tl), predta_kill_non_coacc_rec_def_2 d l tl l0 -> predta_kill_non_coacc_rec_def_1 d s (app c tl) (rec_st d s c tl l e l0).
Proof.
unfold predta_kill_non_coacc_rec_def_1, predta_kill_non_coacc_rec_def_2 in |- *.
intros.
Admitted.

Lemma predta_kill_non_coacc_rec_2 : forall d : preDTA, predta_kill_non_coacc_rec_def_2 d prec_empty tnil (rec_empty d).
Proof.
unfold predta_kill_non_coacc_rec_def_2 in |- *.
intros.
Admitted.

Lemma predta_kill_non_coacc_rec_3 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (r : reconnaissance d a hd), predta_kill_non_coacc_rec_def_0 d a hd r -> forall l : liste_reconnait d la tl, predta_kill_non_coacc_rec_def_2 d la tl l -> predta_kill_non_coacc_rec_def_2 d (prec_cons a la ls) (tcons hd tl) (rec_consi d a la ls hd tl r l).
Proof.
unfold predta_kill_non_coacc_rec_def_0, predta_kill_non_coacc_rec_def_2 in |- *.
intros.
Admitted.

Lemma predta_kill_non_coacc_rec_4 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (l : liste_reconnait d ls (tcons hd tl)), predta_kill_non_coacc_rec_def_2 d ls (tcons hd tl) l -> predta_kill_non_coacc_rec_def_2 d (prec_cons a la ls) (tcons hd tl) (rec_consn d a la ls hd tl l).
Proof.
unfold predta_kill_non_coacc_rec_def_2 in |- *.
intros.
Admitted.

Lemma predta_kill_non_coacc_rev : forall (p : preDTA) (a : ad) (t : term) (m : Map bool), reconnaissance (non_coacc_kill p m) a t -> ensemble_base state p m -> reconnaissance p a t.
Proof.
intros.
Admitted.

Lemma rec_co_0 : forall (d : preDTA) (a b : ad) (t : term) (ladj : state) (e : MapGet state d a = Some ladj) (s : state_reconnait_co d ladj b t), rec_co_def_1 d ladj b t s -> forall c : coacc d b a, rec_co_def_0 d a b t (rec_co_dta d a b t ladj e s c).
Proof.
unfold rec_co_def_1, rec_co_def_0 in |- *.
intros.
Admitted.

Lemma rec_co_1 : forall (d : preDTA) (s : state) (c b : ad) (tl : term_list) (l : prec_list) (e : MapGet prec_list s c = Some l) (l0 : liste_reconnait_co d l b tl), rec_co_def_2 d l b tl l0 -> rec_co_def_1 d s b (app c tl) (rec_co_st d s c b tl l e l0).
Proof.
unfold rec_co_def_2, rec_co_def_1 in |- *.
intros.
Admitted.

Lemma rec_co_2 : forall (d : preDTA) (b : ad), rec_co_def_2 d prec_empty b tnil (rec_co_empty d b).
Proof.
unfold rec_co_def_2 in |- *.
intros.
Admitted.

Lemma predta_kill_non_coacc_2 : forall (d : preDTA) (a0 a1 a2 : ad) (s1 s2 : state) (pl : prec_list) (c : ad), MapGet state d a2 = Some s2 -> MapGet state d a1 = Some s1 -> MapGet prec_list s1 c = Some pl -> prec_occur pl a2 -> coacc d a0 a1 -> predta_kill_non_coacc_def_0 d a0 a1 -> predta_kill_non_coacc_def_0 d a0 a2.
Proof.
unfold predta_kill_non_coacc_def_0 in |- *.
intros.
apply (coacc_nxt (predta_kill_non_coacc d a0) a0 a1 a2 s1 s2 pl c).
elim (predta_kill_non_coacc_0 d a0 a2 s2 H5).
intros.
apply H7.
split.
exact H.
exact H6.
elim (predta_kill_non_coacc_0 d a0 a1 s1 H5).
intros.
apply H7.
split; assumption.
exact H1.
exact H2.
exact (H4 H5 H3).
