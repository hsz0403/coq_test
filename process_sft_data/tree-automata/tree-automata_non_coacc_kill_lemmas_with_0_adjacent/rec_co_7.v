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

Lemma rec_co_7 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list), reconnaissance d a hd -> liste_reconnait d la tl -> rec_co_def_4 d la tl -> rec_co_def_4 d (prec_cons a la ls) (tcons hd tl).
Proof.
unfold rec_co_def_4 in |- *.
intros.
apply (rec_co_consi d a la ls hd a0 tl).
exact (rec_co_5 d a a0 a hd (H4 hd (tlo_head hd hd tl (to_eq hd)) d a H2 H) (H5 a (prec_hd a la ls))).
apply (H1 a0 H2 H0).
intros.
exact (H4 u (tlo_tail u hd tl H6) d0 a1 H7 H8).
intros.
exact (H5 _ (prec_int0 a b la ls H6)).
