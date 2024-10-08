Require Import Bool.
Require Import Arith.
Require Import ZArith.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Import bases.
Inductive term : Set := app : ad -> term_list -> term with term_list : Set := | tnil : term_list | tcons : term -> term_list -> term_list.
Scheme term_term_list_rec := Induction for term Sort Set with term_list_term_rec := Induction for term_list Sort Set.
Scheme term_term_list_ind := Induction for term Sort Prop with term_list_term_ind := Induction for term_list Sort Prop.
Fixpoint lst_length (l : term_list) : nat := match l with | tnil => 0 | tcons _ l' => S (lst_length l') end.
Fixpoint term_high (t : term) : nat := match t with | app a l => S (term_high_0 l) end with term_high_0 (l : term_list) : nat := match l with | tnil => 0 | tcons hd tl => max (term_high hd) (term_high_0 tl) end.
Fixpoint taille_term (t : term) : nat := match t with | app c l => S (mtaille_term_list l) end with mtaille_term_list (l : term_list) : nat := match l with | tnil => 0 | tcons hd tl => max (taille_term hd) (mtaille_term_list tl) end.
Inductive prec_list : Set := | prec_cons : ad -> prec_list -> prec_list -> prec_list | prec_empty : prec_list.
Definition state := Map prec_list.
Definition preDTA := Map state.
Inductive DTA : Set := dta : preDTA -> ad -> DTA.
Fixpoint taille_0 (l : prec_list) : nat := match l with | prec_empty => 0 | prec_cons x y z => S (taille_0 y + taille_0 z) end.
Fixpoint taille_1 (s : state) : nat := match s with | M0 => 0 | M1 x y => taille_0 y | M2 x y => max (taille_1 x) (taille_1 y) end.
Fixpoint DTA_taille (d : preDTA) : nat := match d with | M0 => 0 | M1 x y => taille_1 y | M2 x y => max (DTA_taille x) (DTA_taille y) end.
Inductive prec_occur : prec_list -> ad -> Prop := | prec_hd : forall (a : ad) (pl0 pl1 : prec_list), prec_occur (prec_cons a pl0 pl1) a | prec_int0 : forall (a b : ad) (pl0 pl1 : prec_list), prec_occur pl0 b -> prec_occur (prec_cons a pl0 pl1) b | prec_int1 : forall (a b : ad) (pl0 pl1 : prec_list), prec_occur pl1 b -> prec_occur (prec_cons a pl0 pl1) b.
Inductive prec_contained : prec_list -> prec_list -> Prop := | prec_id : forall p : prec_list, prec_contained p p | prec_c_int0 : forall (p p0 p1 : prec_list) (a : ad), prec_contained p p0 -> prec_contained p (prec_cons a p0 p1) | prec_c_int1 : forall (p p0 p1 : prec_list) (a : ad), prec_contained p p1 -> prec_contained p (prec_cons a p0 p1).
Definition state_in_dta (d : preDTA) (s : state) : Prop := exists a : ad, MapGet state d a = Some s.
Definition state_in_dta_diff (d : preDTA) (s : state) (a : ad) : Prop := exists b : ad, MapGet state d b = Some s /\ a <> b.
Definition prec_in_dta (d : preDTA) (p : prec_list) : Prop := exists s : state, (exists a : ad, (exists c : ad, MapGet state d a = Some s /\ MapGet prec_list s c = Some p)).
Definition prec_in_dta_cont (d : preDTA) (p : prec_list) : Prop := exists s : state, (exists b : ad, (exists c : ad, (exists p0 : prec_list, MapGet state d b = Some s /\ MapGet prec_list s c = Some p0 /\ prec_contained p p0))).
Definition prec_in_dta_diff (d : preDTA) (p : prec_list) (a : ad) : Prop := exists s : state, (exists b : ad, (exists c : ad, MapGet state d b = Some s /\ MapGet prec_list s c = Some p /\ a <> b)).
Definition prec_in_dta_diff_cont (d : preDTA) (p : prec_list) (a : ad) : Prop := exists s : state, (exists b : ad, (exists c : ad, (exists p0 : prec_list, MapGet state d b = Some s /\ MapGet prec_list s c = Some p0 /\ prec_contained p p0 /\ a <> b))).
Definition prec_in_state (s : state) (p : prec_list) : Prop := exists c : ad, MapGet prec_list s c = Some p.
Inductive term_occur : term -> term -> Prop := | to_eq : forall t : term, term_occur t t | to_st : forall (t : term) (a : ad) (tl : term_list), term_list_occur t tl -> term_occur t (app a tl) with term_list_occur : term -> term_list -> Prop := | tlo_head : forall (t hd : term) (tl : term_list), term_occur t hd -> term_list_occur t (tcons hd tl) | tlo_tail : forall (t hd : term) (tl : term_list), term_list_occur t tl -> term_list_occur t (tcons hd tl).
Definition term_occur_def_0 (t : term) := forall u : term, term_occur u t -> term_high u <= term_high t.
Definition term_occur_def_1 (t : term_list) := forall u : term, term_list_occur u t -> term_high u <= term_high_0 t.
Definition indprinciple_3_aux (n : nat) := forall P : term -> Prop, (forall (a : ad) (tl : term_list), (forall u : term, term_list_occur u tl -> P u) -> P (app a tl)) -> forall t : term, term_high t <= n -> P t.

Lemma term_list_disj : forall l : term_list, l = tnil \/ (exists hd : term, (exists tl : term_list, l = tcons hd tl)).
Proof.
simple induction l.
left.
trivial.
right.
split with t.
split with t0.
Admitted.

Lemma high_aux_0 : forall (a : ad) (l : term_list), S (term_high_0 l) <= term_high (app a l).
Proof.
intros.
unfold term_high in |- *.
unfold term_high_0 in |- *.
Admitted.

Lemma high_aux_1 : forall (a : ad) (l : term_list), S (term_high_0 l) = term_high (app a l).
Proof.
intros.
unfold term_high in |- *.
unfold term_high_0 in |- *.
Admitted.

Lemma high_aux_2 : forall (l : term_list) (c : ad), 1 <= term_high (app c l).
Proof.
intros.
cut (S (term_high_0 l) <= term_high (app c l)).
intro.
cut (1 <= S (term_high_0 l)).
intro.
exact (le_trans 1 (S (term_high_0 l)) (term_high (app c l)) H0 H).
exact (le_n_S 0 (term_high_0 l) (le_O_n (term_high_0 l))).
Admitted.

Lemma high_aux_3 : forall (t : term) (tl : term_list), term_high t <= term_high_0 (tcons t tl).
Proof.
intros.
simpl in |- *.
unfold term_high in |- *.
Admitted.

Lemma high_aux_4 : forall (t : term) (tl : term_list), term_high_0 tl <= term_high_0 (tcons t tl).
Proof.
intros.
cut (term_high_0 (tcons t tl) = max (term_high t) (term_high_0 tl)).
intro.
rewrite H.
exact (le_max_r (term_high t) (term_high_0 tl)).
unfold term_high_0 in |- *.
Admitted.

Lemma pl_sum : forall pl : prec_list, pl = prec_empty \/ (exists a : ad, (exists la : prec_list, (exists ls : prec_list, pl = prec_cons a la ls))).
Proof.
intros.
induction pl as [a pl1 Hrecpl1 pl0 Hrecpl0| ].
right.
split with a.
split with pl1.
split with pl0.
reflexivity.
left.
Admitted.

Lemma taille_aux_0 : forall (a : ad) (la ls : prec_list), S (taille_0 la) <= taille_0 (prec_cons a la ls).
Proof.
intros.
simpl in |- *.
apply (le_n_S (taille_0 la) (taille_0 la + taille_0 ls)).
Admitted.

Lemma taille_aux_1 : forall (a : ad) (la ls : prec_list), 1 <= taille_0 (prec_cons a la ls).
Proof.
intros.
unfold taille_0 in |- *.
Admitted.

Lemma taille_aux_2 : forall (a : ad) (la ls : prec_list), S (taille_0 ls) <= taille_0 (prec_cons a la ls).
Proof.
intros.
simpl in |- *.
apply (le_n_S (taille_0 ls) (taille_0 la + taille_0 ls)).
Admitted.

Lemma state_in_dta_M0_false : forall s : state, ~ state_in_dta (M0 state) s.
Proof.
intros.
Admitted.

Lemma prec_occur_1 : forall (a : ad) (p0 p1 p2 : prec_list), prec_contained (prec_cons a p0 p1) p2 -> prec_occur p2 a.
Proof.
intros.
induction p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ].
inversion H.
exact (prec_hd a0 p2_1 p2_0).
exact (prec_int0 a0 a p2_1 p2_0 (Hrecp2_1 H2)).
exact (prec_int1 a0 a p2_1 p2_0 (Hrecp2_0 H2)).
Admitted.

Lemma prec_contained_0 : forall (a : ad) (p0 p1 p2 : prec_list), prec_contained (prec_cons a p0 p1) p2 -> prec_contained p0 p2.
Proof.
intros.
induction p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ].
inversion H.
exact (prec_c_int0 p2_1 p2_1 p2_0 a0 (prec_id p2_1)).
exact (prec_c_int0 _ _ _ _ (Hrecp2_1 H2)).
exact (prec_c_int1 _ _ _ _ (Hrecp2_0 H2)).
Admitted.

Lemma prec_contained_1 : forall (a : ad) (p0 p1 p2 : prec_list), prec_contained (prec_cons a p0 p1) p2 -> prec_contained p1 p2.
Proof.
intros.
induction p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ].
inversion H.
exact (prec_c_int1 _ _ _ _ (prec_id p2_0)).
exact (prec_c_int0 _ _ _ _ (Hrecp2_1 H2)).
exact (prec_c_int1 _ _ _ _ (Hrecp2_0 H2)).
Admitted.

Lemma term_occur_0_0 : forall (a : ad) (t : term_list), term_occur_def_1 t -> term_occur_def_0 (app a t).
Proof.
unfold term_occur_def_1 in |- *.
unfold term_occur_def_0 in |- *.
intros.
inversion H0.
exact (le_n_n _).
apply (le_trans (term_high u) (term_high_0 t) (term_high (app a t)) (H u H3)).
unfold term_high in |- *.
Admitted.

Lemma term_occur_0_1 : term_occur_def_1 tnil.
Proof.
unfold term_occur_def_1 in |- *.
intros.
induction u as (a, t).
Admitted.

Lemma term_occur_0_2 : forall t : term, term_occur_def_0 t -> forall t0 : term_list, term_occur_def_1 t0 -> term_occur_def_1 (tcons t t0).
Proof.
unfold term_occur_def_0 in |- *.
unfold term_occur_def_1 in |- *.
intros.
inversion H1.
apply (le_trans (term_high u) (term_high t) (term_high_0 (tcons t t0))).
exact (H u H4).
exact (le_max_l _ _).
apply (le_trans (term_high u) (term_high_0 t0) (term_high_0 (tcons t t0))).
exact (H0 u H4).
Admitted.

Lemma term_occur_0 : forall t u : term, term_occur u t -> term_high u <= term_high t.
Proof.
Admitted.

Lemma term_occur_1 : forall (t : term_list) (u : term), term_list_occur u t -> term_high u <= term_high_0 t.
Proof.
Admitted.

Lemma indprinciple_3_0 : indprinciple_3_aux 0.
Proof.
unfold indprinciple_3_aux in |- *.
intros.
induction t as (a, t).
simpl in H0.
Admitted.

Lemma prec_in_state_M0_false : forall p : prec_list, ~ prec_in_state (M0 prec_list) p.
Proof.
intros.
exact (in_M0_false prec_list p).
