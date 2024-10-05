Require Import Bool.
Require Import Arith.
Require Import Classical_Prop.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Unset Standard Proposition Elimination Names.
Fixpoint rec_term (d : preDTA) (a : ad) (t : term) (n : nat) {struct n} : bool := match n with | O => false | S k => match t with | app c l => match MapGet _ d a with | None => false | Some lts => match MapGet _ lts c with | None => false | Some pre => rec_list_terms d pre l k end end end end with rec_list_terms (d : preDTA) (pre : prec_list) (l : term_list) (n : nat) {struct n} : bool := match n with | O => false | S k => match pre with | prec_empty => match l with | tnil => true | _ => false end | prec_cons st stp pre' => match l with | tnil => false | tcons hd tl => rec_list_terms d pre' l k || rec_term d st hd k && rec_list_terms d stp tl k end end end.
Definition essence (t : term) (d : preDTA) : nat := S (term_high t) * S (DTA_taille d).
Definition essence_list (l : term_list) (d : preDTA) (pl : prec_list) : nat := match l, pl with | tnil, _ => 1 | _, prec_empty => 1 | _, prec_cons a la ls => taille_0 pl + S (term_high_0 l) * S (DTA_taille d) end.
Definition dta_rec_term (d : DTA) (t : term) : bool := match d with | dta p a => rec_term p a t (essence t p) end.
Inductive reconnaissance : preDTA -> ad -> term -> Prop := rec_dta : forall (d : preDTA) (a : ad) (t : term) (ladj : state), MapGet state d a = Some ladj -> state_reconnait d ladj t -> reconnaissance d a t with state_reconnait : preDTA -> state -> term -> Prop := rec_st : forall (d : preDTA) (s : state) (c : ad) (tl : term_list) (l : prec_list), MapGet prec_list s c = Some l -> liste_reconnait d l tl -> state_reconnait d s (app c tl) with liste_reconnait : preDTA -> prec_list -> term_list -> Prop := | rec_empty : forall d : preDTA, liste_reconnait d prec_empty tnil | rec_consi : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list), reconnaissance d a hd -> liste_reconnait d la tl -> liste_reconnait d (prec_cons a la ls) (tcons hd tl) | rec_consn : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list), liste_reconnait d ls (tcons hd tl) -> liste_reconnait d (prec_cons a la ls) (tcons hd tl).
Definition reconnait (d : DTA) (t : term) : Prop := match d with | dta p a => reconnaissance p a t end.
Scheme mreconnaissance_ind := Induction for reconnaissance Sort Prop with mstrec_ind := Induction for state_reconnait Sort Prop with mlrec_ind := Induction for liste_reconnait Sort Prop.
Definition sem_equiv_prop_t (t : term) := forall (d : preDTA) (a : ad) (n : nat), rec_term d a t n = true -> reconnaissance d a t.
Definition sem_equiv_prop_l (l : term_list) := forall (d : preDTA) (p : prec_list) (n : nat), rec_list_terms d p l n = true -> liste_reconnait d p l.
Definition invar_term (t : term) : Prop := forall (n m : nat) (d : preDTA) (a : ad), rec_term d a t n = true -> n <= m -> rec_term d a t m = true.
Definition invar_list (tl : term_list) : Prop := forall (n m : nat) (d : preDTA) (p : prec_list), rec_list_terms d p tl n = true -> n <= m -> rec_list_terms d p tl m = true.
Definition dta_reconnait (d : preDTA) (a : ad) (t : term) (pr : reconnaissance d a t) := rec_term d a t (essence t d) = true.
Definition st_reconnait (d : preDTA) (s : state) (t : term) (pr : state_reconnait d s t) := match t with | app c l => exists p : prec_list, MapGet prec_list s c = Some p /\ rec_list_terms d p l (essence_list l d p) = true end.
Definition pre_reconnait (d : preDTA) (p : prec_list) (t : term_list) (pr : liste_reconnait d p t) := rec_list_terms d p t (essence_list t d p) = true.

Lemma borne_0_0 : forall p : prec_list, prec_in_state (M0 prec_list) p -> taille_0 p <= taille_1 (M0 prec_list).
Proof.
intros.
elim (prec_in_state_M0_false p).
Admitted.

Lemma borne_0_2 : forall (m0 m1 : Map prec_list) (p : prec_list), (prec_in_state m0 p -> taille_0 p <= taille_1 m0) -> (prec_in_state m1 p -> taille_0 p <= taille_1 m1) -> prec_in_state (M2 prec_list m0 m1) p -> taille_0 p <= taille_1 (M2 prec_list m0 m1).
Proof.
intros.
cut (prec_in_state m0 p \/ prec_in_state m1 p).
intro.
elim H2; intros.
simpl in |- *.
cut (taille_0 p <= taille_1 m0).
intro.
cut (taille_1 m0 <= max (taille_1 m0) (taille_1 m1)).
intro.
exact (le_trans (taille_0 p) (taille_1 m0) (max (taille_1 m0) (taille_1 m1)) H4 H5).
exact (le_max_l (taille_1 m0) (taille_1 m1)).
exact (H H3).
simpl in |- *.
cut (taille_0 p <= taille_1 m1).
cut (taille_1 m1 <= max (taille_1 m0) (taille_1 m1)).
intros.
exact (le_trans (taille_0 p) (taille_1 m1) (max (taille_1 m0) (taille_1 m1)) H5 H4).
exact (le_max_r (taille_1 m0) (taille_1 m1)).
exact (H0 H3).
unfold prec_in_state in |- *.
unfold prec_in_state in H1.
Admitted.

Lemma borne_0 : forall (s : state) (p : prec_list), prec_in_state s p -> taille_0 p <= taille_1 s.
Proof.
simple induction s.
intros.
exact (borne_0_0 p H).
intros.
exact (borne_0_1 a a0 p H).
intros.
Admitted.

Lemma borne_1_0 : forall s : state, state_in_dta (M0 state) s -> taille_1 s <= DTA_taille (M0 state).
Proof.
intros.
elim (state_in_dta_M0_false s).
Admitted.

Lemma borne_1_1 : forall (a : ad) (s' s : state), state_in_dta (M1 state a s') s -> taille_1 s <= DTA_taille (M1 state a s').
Proof.
intros.
cut (s = s').
intros.
simpl in |- *.
rewrite H0.
exact (le_n_n (taille_1 s')).
unfold state_in_dta in H.
Admitted.

Lemma borne_1_2 : forall (m0 m1 : Map state) (s : state), (state_in_dta m0 s -> taille_1 s <= DTA_taille m0) -> (state_in_dta m1 s -> taille_1 s <= DTA_taille m1) -> state_in_dta (M2 state m0 m1) s -> taille_1 s <= DTA_taille (M2 state m0 m1).
Proof.
intros.
cut (state_in_dta m0 s \/ state_in_dta m1 s).
intro.
elim H2; intros.
simpl in |- *.
cut (taille_1 s <= DTA_taille m0).
intro.
cut (DTA_taille m0 <= max (DTA_taille m0) (DTA_taille m1)).
intro.
exact (le_trans (taille_1 s) (DTA_taille m0) (max (DTA_taille m0) (DTA_taille m1)) H4 H5).
exact (le_max_l (DTA_taille m0) (DTA_taille m1)).
exact (H H3).
simpl in |- *.
cut (taille_1 s <= DTA_taille m1).
cut (DTA_taille m1 <= max (DTA_taille m0) (DTA_taille m1)).
intros.
exact (le_trans (taille_1 s) (DTA_taille m1) (max (DTA_taille m0) (DTA_taille m1)) H5 H4).
exact (le_max_r (DTA_taille m0) (DTA_taille m1)).
exact (H0 H3).
unfold state_in_dta in |- *.
unfold state_in_dta in H1.
Admitted.

Lemma borne_1 : forall (d : preDTA) (s : state), state_in_dta d s -> taille_1 s <= DTA_taille d.
Proof.
simple induction d.
intros.
exact (borne_1_0 s H).
intros.
exact (borne_1_1 a a0 s H).
intros.
Admitted.

Lemma borne_2 : forall (d : preDTA) (p : prec_list), prec_in_dta d p -> taille_0 p <= DTA_taille d.
Proof.
intros.
unfold prec_in_dta in H.
elim H.
intros.
elim H0.
intros.
elim H1.
intros.
elim H2.
intros.
cut (taille_0 p <= taille_1 x).
cut (taille_1 x <= DTA_taille d).
intros.
exact (le_trans (taille_0 p) (taille_1 x) (DTA_taille d) H6 H5).
apply (borne_1 d x).
unfold state_in_dta in |- *.
split with x0.
assumption.
apply (borne_0 x p).
unfold prec_in_state in |- *.
split with x1.
Admitted.

Lemma conservation_0_0 : forall n n0 : nat, S n * S n0 = S (n0 + n * S n0).
Proof.
simple induction n.
simpl in |- *.
trivial.
intros.
simpl in |- *.
Admitted.

Lemma conservation_0 : forall (d : preDTA) (p : prec_list) (c : ad) (l : term_list), prec_in_dta d p -> S (essence_list l d p) <= essence (app c l) d.
Proof.
intro.
intro.
intro.
simple induction l.
intros.
unfold essence_list in |- *.
unfold essence in |- *.
case p.
intros.
cut (2 <= S (term_high (app c tnil))).
cut (1 <= S (DTA_taille d)).
intros.
exact (le_mult_mult 2 (S (term_high (app c tnil))) 1 (S (DTA_taille d)) H1 H0).
exact (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d))).
cut (1 <= term_high (app c tnil)).
intro.
exact (le_n_S 1 (term_high (app c tnil)) H0).
simpl in |- *.
exact (le_n_n 1).
intros.
cut (2 <= S (term_high (app c tnil))).
cut (1 <= S (DTA_taille d)).
intros.
exact (le_mult_mult 2 (S (term_high (app c tnil))) 1 (S (DTA_taille d)) H1 H0).
exact (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d))).
cut (1 <= term_high (app c tnil)).
intro.
exact (le_n_S 1 (term_high (app c tnil)) H0).
simpl in |- *.
exact (le_n_n 1).
case p.
intros.
unfold essence in |- *.
unfold essence_list in |- *.
cut (S (term_high (app c (tcons t t0))) * S (DTA_taille d) = S (DTA_taille d + term_high (app c (tcons t t0)) * S (DTA_taille d))).
intro.
rewrite H1.
cut (taille_0 (prec_cons a p0 p1) + S (term_high_0 (tcons t t0)) * S (DTA_taille d) <= DTA_taille d + term_high (app c (tcons t t0)) * S (DTA_taille d)).
intro.
exact (le_n_S _ _ H2).
cut (taille_0 (prec_cons a p0 p1) <= DTA_taille d).
cut (S (term_high_0 (tcons t t0)) * S (DTA_taille d) <= term_high (app c (tcons t t0)) * S (DTA_taille d)).
intros.
exact (plus_le_compat _ _ _ _ H3 H2).
cut (S (term_high_0 (tcons t t0)) <= term_high (app c (tcons t t0))).
intro.
exact (le_mult_l _ _ _ H2).
cut (S (term_high_0 (tcons t t0)) = term_high (app c (tcons t t0))).
intro.
exact (high_aux_0 c (tcons t t0)).
exact (high_aux_1 c (tcons t t0)).
exact (borne_2 d (prec_cons a p0 p1) H0).
exact (conservation_0_0 (term_high (app c (tcons t t0))) (DTA_taille d)).
intros.
unfold essence_list in |- *.
unfold essence in |- *.
cut (2 <= S (term_high (app c (tcons t t0)))).
cut (1 <= S (DTA_taille d)).
intros.
exact (le_mult_mult 2 (S (term_high (app c (tcons t t0)))) 1 (S (DTA_taille d)) H2 H1).
exact (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d))).
apply (le_n_S 1 (term_high (app c (tcons t t0)))).
cut (1 <= S (term_high_0 (tcons t t0))).
cut (S (term_high_0 (tcons t t0)) <= term_high (app c (tcons t t0))).
intros.
exact (le_trans 1 (S (term_high_0 (tcons t t0))) (term_high (app c (tcons t t0))) H2 H1).
exact (high_aux_0 c (tcons t t0)).
apply (le_n_S 0 (term_high_0 (tcons t t0))).
Admitted.

Lemma conservation_1 : forall (d : preDTA) (l : term_list), 1 <= essence_list l d prec_empty.
Proof.
intros.
induction l as [| t l Hrecl].
simpl in |- *.
exact (le_n_n 1).
simpl in |- *.
Admitted.

Lemma conservation_2 : forall (d : preDTA) (p : prec_list), 1 <= essence_list tnil d p.
Proof.
intros.
simpl in |- *.
Admitted.

Lemma conservation_3 : forall (d : preDTA) (hd : term) (tl : term_list) (a : ad) (la ls : prec_list), S (essence_list (tcons hd tl) d ls) <= essence_list (tcons hd tl) d (prec_cons a la ls).
Proof.
unfold essence_list in |- *.
intros.
induction ls as [a0 ls1 Hrecls1 ls0 Hrecls0| ].
cut (S (taille_0 (prec_cons a0 ls1 ls0) + S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) = S (taille_0 (prec_cons a0 ls1 ls0)) + S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
intro.
rewrite H.
cut (S (taille_0 (prec_cons a0 ls1 ls0)) <= taille_0 (prec_cons a la (prec_cons a0 ls1 ls0))).
intro.
exact (plus_le_compat (S (taille_0 (prec_cons a0 ls1 ls0))) (taille_0 (prec_cons a la (prec_cons a0 ls1 ls0))) (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) H0 (le_n_n (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)))).
exact (taille_aux_2 a la (prec_cons a0 ls1 ls0)).
generalize (taille_0 (prec_cons a0 ls1 ls0)).
generalize (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
simpl in |- *.
trivial.
cut (1 <= taille_0 (prec_cons a la prec_empty)).
cut (1 <= S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
intros.
exact (plus_le_compat 1 (taille_0 (prec_cons a la prec_empty)) 1 (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) H0 H).
exact (le_mult_mult 1 (S (term_high_0 (tcons hd tl))) 1 (S (DTA_taille d)) (le_n_S 0 (term_high_0 (tcons hd tl)) (le_O_n (term_high_0 (tcons hd tl)))) (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d)))).
Admitted.

Lemma conservation_4 : forall (d : preDTA) (hd : term) (tl : term_list) (a : ad) (la ls : prec_list), S (essence_list tl d la) <= essence_list (tcons hd tl) d (prec_cons a la ls).
Proof.
unfold essence_list in |- *.
intro.
intro.
intro.
intros.
cut (1 <= taille_0 (prec_cons a la ls)).
cut (1 <= S (term_high_0 (tcons hd tl)) * S (DTA_taille d)).
intros.
induction tl as [| t tl Hrectl].
cut (2 <= taille_0 (prec_cons a la ls) + S (term_high_0 (tcons hd tnil)) * S (DTA_taille d)).
intros.
induction la as [a0 la1 Hrecla1 la0 Hrecla0| ].
assumption.
assumption.
exact (plus_le_compat 1 (taille_0 (prec_cons a la ls)) 1 (S (term_high_0 (tcons hd tnil)) * S (DTA_taille d)) H0 H).
induction la as [a0 la1 Hrecla1 la0 Hrecla0| ].
cut (S (taille_0 (prec_cons a0 la1 la0) + S (term_high_0 (tcons t tl)) * S (DTA_taille d)) = S (taille_0 (prec_cons a0 la1 la0)) + S (term_high_0 (tcons t tl)) * S (DTA_taille d)).
intro.
rewrite H1.
cut (S (taille_0 (prec_cons a0 la1 la0)) <= taille_0 (prec_cons a (prec_cons a0 la1 la0) ls)).
intro.
apply (plus_le_compat (S (taille_0 (prec_cons a0 la1 la0))) (taille_0 (prec_cons a (prec_cons a0 la1 la0) ls)) (S (term_high_0 (tcons t tl)) * S (DTA_taille d)) (S (term_high_0 (tcons hd (tcons t tl))) * S (DTA_taille d)) H2).
cut (S (term_high_0 (tcons t tl)) <= S (term_high_0 (tcons hd (tcons t tl)))).
intro.
exact (le_mult_mult (S (term_high_0 (tcons t tl))) (S (term_high_0 (tcons hd (tcons t tl)))) (S (DTA_taille d)) (S (DTA_taille d)) H3 (le_n_n (S (DTA_taille d)))).
exact (le_n_S (term_high_0 (tcons t tl)) (term_high_0 (tcons hd (tcons t tl))) (high_aux_4 hd (tcons t tl))).
exact (taille_aux_0 a (prec_cons a0 la1 la0) ls).
generalize (taille_0 (prec_cons a0 la1 la0)).
generalize (S (term_high_0 (tcons t tl)) * S (DTA_taille d)).
simpl in |- *.
trivial.
exact (plus_le_compat 1 (taille_0 (prec_cons a prec_empty ls)) 1 (S (term_high_0 (tcons hd (tcons t tl))) * S (DTA_taille d)) H0 H).
exact (le_mult_mult 1 (S (term_high_0 (tcons hd tl))) 1 (S (DTA_taille d)) (le_n_S 0 (term_high_0 (tcons hd tl)) (le_O_n (term_high_0 (tcons hd tl)))) (le_n_S 0 (DTA_taille d) (le_O_n (DTA_taille d)))).
Admitted.

Lemma conservation_5_0 : forall (a : ad) (la ls : prec_list), 1 <= taille_0 (prec_cons a la ls).
Proof.
intros.
simpl in |- *.
apply (le_n_S 0 (taille_0 la + taille_0 ls)).
Admitted.

Lemma conservation_5 : forall (d : preDTA) (hd : term) (tl : term_list) (a : ad) (la ls : prec_list), S (essence hd d) <= essence_list (tcons hd tl) d (prec_cons a la ls).
Proof.
intros.
unfold essence in |- *.
unfold essence_list in |- *.
cut (term_high hd <= term_high_0 (tcons hd tl)).
cut (1 <= taille_0 (prec_cons a la ls)).
intros.
cut (S (S (term_high hd) * S (DTA_taille d)) = 1 + S (term_high hd) * S (DTA_taille d)).
intros.
rewrite H1.
apply (plus_le_compat 1 (taille_0 (prec_cons a la ls)) (S (term_high hd) * S (DTA_taille d)) (S (term_high_0 (tcons hd tl)) * S (DTA_taille d)) H).
apply (le_mult_mult (S (term_high hd)) (S (term_high_0 (tcons hd tl))) (S (DTA_taille d)) (S (DTA_taille d)) (le_n_S (term_high hd) (term_high_0 (tcons hd tl)) H0)).
exact (le_n_n (S (DTA_taille d))).
unfold plus in |- *.
trivial.
exact (conservation_5_0 a la ls).
Admitted.

Lemma sem_listes_0 : forall (d : preDTA) (p : prec_list) (hd : term) (tl : term_list), liste_reconnait d p (tcons hd tl) -> p <> prec_empty.
Proof.
intros.
intro.
inversion H.
rewrite H0 in H4.
discriminate H4.
rewrite H0 in H3.
Admitted.

Lemma sem_listes_1 : forall (d : preDTA) (hd : term) (tl : term_list), ~ liste_reconnait d prec_empty (tcons hd tl).
Proof.
intros.
intro.
cut (prec_empty = prec_empty).
intro.
exact (sem_listes_0 d prec_empty hd tl H H0).
Admitted.

Lemma sem_listes_2 : forall (d : preDTA) (pl : prec_list), liste_reconnait d pl tnil -> pl = prec_empty.
Proof.
intros.
inversion H.
Admitted.

Lemma semantic_equiv_0_0 : forall (d : preDTA) (p : prec_list) (n : nat), rec_list_terms d p tnil n = true -> p = prec_empty.
Proof.
intros.
induction p as [a p1 Hrecp1 p0 Hrecp0| ].
induction n as [| n Hrecn].
simpl in H.
discriminate H.
simpl in H.
discriminate H.
Admitted.

Lemma semantic_equiv_0_1 : sem_equiv_prop_l tnil.
Proof.
unfold sem_equiv_prop_l in |- *.
intros.
cut (p = prec_empty).
intros.
rewrite H0.
exact (rec_empty d).
Admitted.

Lemma borne_0_1 : forall (a : ad) (p' p : prec_list), prec_in_state (M1 prec_list a p') p -> taille_0 p <= taille_1 (M1 prec_list a p').
Proof.
intros.
cut (p = p').
intros.
simpl in |- *.
rewrite H0.
exact (le_n_n (taille_0 p')).
unfold prec_in_state in H.
exact (in_M1_id prec_list p a p' H).
