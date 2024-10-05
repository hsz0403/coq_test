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

Lemma invar_2 : forall t : term, invar_term t -> forall t0 : term_list, invar_list t0 -> invar_list (tcons t t0).
Proof.
intros.
unfold invar_list in H0.
unfold invar_list in |- *.
simple induction n; simple induction m; intro.
intros.
simpl in H1.
discriminate H1.
intros.
simpl in H2.
discriminate H2.
intros.
elim (le_Sn_O n0 H3).
simple induction p.
intros.
cut (rec_list_terms d p1 (tcons t t0) n1 = true \/ rec_term d a t n1 = true /\ rec_list_terms d p0 t0 n1 = true).
intro.
elim H7.
intros.
exact (invar_2_2 d a p0 p1 t t0 n1 H7).
intros.
exact (invar_2_2 d a p0 p1 t t0 n1 H7).
cut (rec_list_terms d p1 (tcons t t0) n0 = true \/ rec_term d a t n0 = true /\ rec_list_terms d p0 t0 n0 = true).
intro.
elim H7; intros.
left.
exact (H1 n1 d p1 H8 (le_S_n n0 n1 H6)).
right.
elim H8.
intros.
split.
unfold invar_term in H.
exact (H n0 n1 d a H9 (le_S_n n0 n1 H6)).
exact (H0 n0 n1 d p0 H10 (le_S_n n0 n1 H6)).
exact (invar_2_1 d a p0 p1 t t0 n0 H5).
intros.
simpl in H3.
discriminate H3.
