Require Import ZArith.
Require Import NArith Ndec.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import lattice_fixpoint.
Require Import signature.
Require Import pl_path.
Require Import empty_test.
Fixpoint prec_list_kill (m : Map bool) (p : prec_list) {struct p} : option prec_list := match p with | prec_empty => Some prec_empty | prec_cons a la ls => match ls with | prec_empty => match MapGet bool m a with | None => None | Some b => if b then match prec_list_kill m la with | None => None | Some la' => Some (prec_cons a la' prec_empty) end else None end | prec_cons _ _ _ => match MapGet bool m a with | None => prec_list_kill m ls | Some b => if b then match prec_list_kill m la, prec_list_kill m ls with | None, None => None | None, Some ls' => Some ls' | Some la', None => Some (prec_cons a la' prec_empty) | Some la', Some ls' => Some (prec_cons a la' ls') end else prec_list_kill m ls end end end.
Fixpoint states_kill_aux (m : Map bool) (s : state) {struct s} : state := match s with | M0 => M0 prec_list | M1 a p => match prec_list_kill m p with | None => M0 prec_list | Some p' => M1 prec_list a p' end | M2 s0 s1 => match states_kill_aux m s0, states_kill_aux m s1 with | M0, M0 => M0 prec_list | M0, M1 a p => M1 prec_list (Ndouble_plus_one a) p | M1 a p, M0 => M1 prec_list (N.double a) p | s0', s1' => M2 prec_list s0' s1' end end.
Definition states_kill (m : Map bool) (s : state) : option state := match states_kill_aux m s with | M0 => None | x => Some x end.
Fixpoint preDTA_kill (m : Map bool) (d : preDTA) {struct d} : preDTA := match d with | M0 => M0 state | M1 a s => match states_kill m s with | None => M0 state | Some s' => M1 state a s' end | M2 d0 d1 => match preDTA_kill m d0, preDTA_kill m d1 with | M0, M0 => M0 state | M0, M1 a s' => M1 state (Ndouble_plus_one a) s' | M1 a s', M0 => M1 state (N.double a) s' | d0', d1' => M2 state d0' d1' end end.
Definition DTA_simpl (d : DTA) : DTA := match d with | dta p a => match MapGet state p a with | None => dta (M1 state N0 (M0 prec_list)) N0 | _ => dta p a end end.
Definition DTA_kill (m : Map bool) (d : DTA) : DTA := match d with | dta p a => DTA_simpl (dta (preDTA_kill m p) a) end.
Definition DTA_kill_empty_states (d : DTA) : DTA := DTA_kill (dta_states_non_empty d) d.
Definition DTA_kill_empty_states_lazy (d : DTA) : DTA := DTA_kill (dta_states_non_empty_lazy d) d.
Definition dt_kill_empty_def_0 (n : nat) : Prop := forall (d : preDTA) (a : ad) (t : term), term_high t <= n -> reconnaissance d a t -> reconnaissance (preDTA_kill (dta_non_empty_states d) d) a t.
Definition dt_kill_empty_def_1 (n : nat) : Prop := forall (d : preDTA) (a : ad) (t : term), term_high t <= n -> reconnaissance (preDTA_kill (dta_non_empty_states d) d) a t -> reconnaissance d a t.

Lemma dt_kill_empty_r_1 : forall (p' : prec_list) (n : nat) (d : preDTA) (p : prec_list) (tl : term_list), dt_kill_empty_def_1 n -> term_high_0 tl <= n -> liste_reconnait (preDTA_kill (dta_non_empty_states d) d) p tl -> prec_list_kill (dta_non_empty_states d) p' = Some p -> liste_reconnait d p' tl.
Proof.
simple induction p'.
intros.
simpl in H4.
elim (pl_sum p0); intros.
rewrite H5 in H4.
elim (option_sum bool (MapGet bool (dta_non_empty_states d) a)); intro y.
elim y.
intros x y0.
rewrite y0 in H4.
elim (bool_is_true_or_false x); intro; rewrite H6 in H4.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p)); intro y1.
elim y1.
intros x0 y2.
rewrite y2 in H4.
inversion H4.
rewrite <- H8 in H3.
inversion H3.
apply (rec_consi d a p p0 hd tl0).
rewrite <- H11 in H2.
exact (H1 _ _ _ (le_trans _ _ _ (le_max_l _ _) H2) H13).
rewrite <- H11 in H2.
exact (H n d x0 tl0 H1 (le_trans _ _ _ (le_max_r _ _) H2) H14 y2).
inversion H13.
rewrite y1 in H4.
inversion H4.
inversion H4.
rewrite y in H4.
inversion H4.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
rewrite H8 in H4.
elim (option_sum bool (MapGet bool (dta_non_empty_states d) a)); intro y.
elim y.
intros x2 y0.
rewrite y0 in H4.
elim (bool_is_true_or_false x2); intros; rewrite H9 in H4.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p)); intro y1.
elim y1.
intros x3 y2.
rewrite y2 in H4.
rewrite <- H8 in H4.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) p0)); intro y3.
elim y3.
intros x4 y4.
rewrite y4 in H4.
inversion H4.
rewrite <- H11 in H3.
inversion H3.
apply (rec_consi d a p p0 hd tl0).
rewrite <- H14 in H2.
exact (H1 _ _ _ (le_trans _ _ _ (le_max_l _ _) H2) H16).
rewrite <- H14 in H2.
exact (H _ _ _ _ H1 (le_trans _ _ _ (le_max_r _ _) H2) H17 y2).
rewrite <- H13 in H2.
apply (rec_consn d a p p0 hd tl0).
exact (H0 n d x4 (tcons hd tl0) H1 H2 H16 y4).
rewrite y3 in H4.
inversion H4.
rewrite <- H11 in H3.
inversion H3.
apply (rec_consi d a p p0 hd tl0).
rewrite <- H14 in H2.
exact (H1 _ _ _ (le_trans _ _ _ (le_max_l _ _) H2) H16).
rewrite <- H14 in H2.
exact (H _ _ _ _ H1 (le_trans _ _ _ (le_max_r _ _) H2) H17 y2).
inversion H16.
rewrite y1 in H4.
elim (option_sum prec_list (prec_list_kill (dta_non_empty_states d) (prec_cons x x0 x1))); intro y2.
elim y2.
intros x3 y3.
rewrite y3 in H4.
inversion H4.
rewrite <- H11 in H3.
rewrite <- H8 in y3.
induction tl as [| t tl Hrectl].
inversion H3.
rewrite <- H12 in y3.
rewrite (pl_kill_prec_empty _ _ y3) in H8.
inversion H8.
apply (rec_consn d a p p0 t tl).
exact (H0 _ _ _ _ H1 H2 H3 y3).
rewrite y2 in H4.
inversion H4.
rewrite <- H8 in H4.
induction tl as [| t tl Hrectl].
inversion H3.
rewrite <- H11 in H4.
rewrite (pl_kill_prec_empty _ _ H4) in H8.
inversion H8.
apply (rec_consn d a p p0 t tl).
exact (H0 _ _ _ _ H1 H2 H3 H4).
rewrite y in H4.
rewrite <- H8 in H4.
induction tl as [| t tl Hrectl].
inversion H3.
rewrite <- H10 in H4.
rewrite (pl_kill_prec_empty _ _ H4) in H8.
inversion H8.
exact (rec_consn d a p p0 t tl (H0 _ _ _ _ H1 H2 H3 H4)).
intros.
simpl in H2.
inversion H2.
rewrite <- H4 in H1.
inversion H1.
exact (rec_empty _).
