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
exact (taille_aux_1 a la ls).
