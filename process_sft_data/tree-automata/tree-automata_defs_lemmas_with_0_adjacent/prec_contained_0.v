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

Lemma prec_contained_0 : forall (a : ad) (p0 p1 p2 : prec_list), prec_contained (prec_cons a p0 p1) p2 -> prec_contained p0 p2.
Proof.
intros.
induction p2 as [a0 p2_1 Hrecp2_1 p2_0 Hrecp2_0| ].
inversion H.
exact (prec_c_int0 p2_1 p2_1 p2_0 a0 (prec_id p2_1)).
exact (prec_c_int0 _ _ _ _ (Hrecp2_1 H2)).
exact (prec_c_int1 _ _ _ _ (Hrecp2_0 H2)).
inversion H.
