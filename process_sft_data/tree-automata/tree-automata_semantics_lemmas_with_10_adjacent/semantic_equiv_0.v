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

Lemma semantic_equiv_0_2 : forall (d : preDTA) (a a' : ad) (l : term_list) (n : nat) (s : state) (p : prec_list), rec_term d a (app a' l) (S n) = true -> MapGet state d a = Some s -> MapGet prec_list s a' = Some p -> rec_list_terms d p l n = true.
Proof.
intro.
intro.
intro.
intro.
simple induction n.
intros.
simpl in H.
rewrite H0 in H.
rewrite H1 in H.
discriminate H.
intros.
elim (classic (rec_list_terms d p l (S n0) = true)).
intro.
assumption.
intro.
cut (rec_list_terms d p l (S n0) = false).
intro.
simpl in H0.
rewrite H1 in H0.
rewrite H2 in H0.
simpl in H0.
simpl in H4.
simpl in H4.
rewrite H4 in H0.
discriminate H0.
Admitted.

Lemma semantic_equiv_0_3 : forall (d : preDTA) (a a' : ad) (l : term_list) (n : nat), rec_term d a (app a' l) (S n) = true -> exists s : state, MapGet state d a = Some s.
Proof.
intro.
intro.
intro.
intro.
simpl in |- *.
intro.
elim (MapGet state d a).
Focus 2.
intro H.
discriminate H.
intro.
split with a0.
Admitted.

Lemma semantic_equiv_0_4 : forall (d : preDTA) (a a' : ad) (l : term_list) (n : nat) (s : state), MapGet state d a = Some s -> rec_term d a (app a' l) (S n) = true -> exists p : prec_list, MapGet prec_list s a' = Some p.
Proof.
intro.
intro.
intro.
intro.
intro.
intro.
intro.
simpl in |- *.
rewrite H.
simpl in |- *.
elim (MapGet prec_list s a').
Focus 2.
intro H0.
discriminate H0.
intro.
intro.
split with a0.
Admitted.

Lemma semantic_equiv_0_5 : forall (a : ad) (t : term_list), sem_equiv_prop_l t -> sem_equiv_prop_t (app a t).
Proof.
unfold sem_equiv_prop_l in |- *.
unfold sem_equiv_prop_t in |- *.
intros.
cut (exists s : state, MapGet state d a0 = Some s).
intro.
elim H1.
intros.
cut (exists p : prec_list, MapGet prec_list x a = Some p).
intros.
elim H3.
intros.
induction n as [| n Hrecn].
simpl in H0.
discriminate H0.
exact (rec_dta d a0 (app a t) x H2 (rec_st d x a t x0 H4 (H d x0 n (semantic_equiv_0_2 d a0 a t n x x0 H0 H2 H4)))).
induction n as [| n Hrecn].
simpl in H0.
discriminate.
exact (semantic_equiv_0_4 d a0 a t n x H2 H0).
induction n as [| n Hrecn].
simpl in H0.
discriminate H0.
Admitted.

Lemma semantic_equiv_0_6 : forall (n : nat) (t : term) (t0 : term_list), (forall (d : preDTA) (a : ad) (m : nat), rec_term d a t m = true -> reconnaissance d a t) -> (forall (d : preDTA) (p : prec_list) (m : nat), rec_list_terms d p t0 m = true -> liste_reconnait d p t0) -> forall (d : preDTA) (p : prec_list), rec_list_terms d p (tcons t t0) n = true -> liste_reconnait d p (tcons t t0).
Proof.
simple induction n.
intros.
simpl in H1.
inversion H1.
intros.
simpl in H2.
elim (pl_sum p); intros.
rewrite H3 in H2.
inversion H2.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
rewrite H6 in H2.
elim (bool_is_true_or_false (rec_list_terms d x1 (tcons t t0) n0)); intros; rewrite H7 in H2.
rewrite H6.
exact (rec_consn d x x0 x1 t t0 (H t t0 H0 H1 d x1 H7)).
simpl in H2.
fold rec_term in H2.
elim (bool_is_true_or_false (rec_term d x t n0)); intros; rewrite H8 in H2.
elim (bool_is_true_or_false (rec_list_terms d x0 t0 n0)).
intros.
rewrite H6.
exact (rec_consi d x x0 x1 t t0 (H0 _ _ _ H8) (H1 _ _ _ H9)).
intros.
rewrite H9 in H2.
inversion H2.
Admitted.

Lemma semantic_equiv_0_7 : forall t : term, sem_equiv_prop_t t -> forall t0 : term_list, sem_equiv_prop_l t0 -> sem_equiv_prop_l (tcons t t0).
Proof.
unfold sem_equiv_prop_t, sem_equiv_prop_l in |- *.
intros.
Admitted.

Lemma invar_0 : invar_list tnil.
Proof.
unfold invar_list in |- *.
simple induction n.
intro.
intro.
simple induction p.
intros.
simpl in H1.
discriminate H1.
intros.
simpl in H.
discriminate H.
intro.
intro.
simple induction m.
intros.
elim (le_Sn_O n0 H1).
intro.
intro.
simple induction p.
intros.
simpl in |- *.
simpl in H3.
assumption.
simpl in |- *.
intros.
Admitted.

Lemma invar_1_0 : forall (d : preDTA) (a c : ad) (t : term_list) (n : nat) (s : state) (p : prec_list), MapGet state d a = Some s -> MapGet prec_list s c = Some p -> rec_list_terms d p t n = true -> rec_term d a (app c t) (S n) = true.
Proof.
intro; intro; intro; simple induction n.
intros.
simpl in H1.
discriminate H1.
intros.
simpl in |- *.
rewrite H0.
rewrite H1.
simpl in H2.
Admitted.

Lemma invar_1_1 : forall (d : preDTA) (a c : ad) (t : term_list) (n : nat), rec_term d a (app c t) (S n) = true -> exists p : prec_list, rec_list_terms d p t n = true.
Proof.
intros.
cut (exists s : state, MapGet state d a = Some s).
intro.
elim H0.
intros.
cut (exists p : prec_list, MapGet prec_list x c = Some p).
intro.
elim H2.
intros.
split with x0.
exact (semantic_equiv_0_2 d a c t n x x0 H H1 H3).
exact (semantic_equiv_0_4 d a c t n x H1 H).
Admitted.

Lemma invar_1 : forall (a : ad) (t : term_list), invar_list t -> invar_term (app a t).
Proof.
intro.
intro.
intro.
unfold invar_list in H.
unfold invar_term in |- *.
simple induction n.
intros.
simpl in H0.
discriminate H0.
intro.
intro.
simple induction m; intros.
elim (le_Sn_O n0 H2).
cut (exists s : state, MapGet state d a0 = Some s).
intro.
elim H4.
intros.
cut (exists p : prec_list, MapGet prec_list x a = Some p).
intro.
elim H6.
intros.
apply (invar_1_0 d a0 a t n1 x x0 H5 H7).
cut (rec_list_terms d x0 t n0 = true).
intro.
exact (H n0 n1 d x0 H8 (le_S_n n0 n1 H3)).
exact (semantic_equiv_0_2 d a0 a t n0 x x0 H2 H5 H7).
exact (semantic_equiv_0_4 d a0 a t n0 x H5 H2).
Admitted.

Lemma invar_2_0 : forall (d : preDTA) (p : prec_list) (n : nat), rec_list_terms d p tnil n = true -> p = prec_empty.
Proof.
intro.
simple induction p; simple induction n.
intro.
simpl in H1.
discriminate H1.
intros.
simpl in H2.
discriminate H2.
intro.
simpl in H.
trivial.
intros.
Admitted.

Lemma invar_2_1 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (n : nat), rec_list_terms d (prec_cons a la ls) (tcons hd tl) (S n) = true -> rec_list_terms d ls (tcons hd tl) n = true \/ rec_term d a hd n = true /\ rec_list_terms d la tl n = true.
Proof.
intro.
intro.
intro.
intro.
intro.
intro.
intro.
induction n as [| n Hrecn].
intro.
simpl in H.
discriminate H.
intros.
cut (rec_list_terms d ls (tcons hd tl) (S n) = true \/ rec_list_terms d ls (tcons hd tl) (S n) = false).
cut (rec_term d a hd (S n) = true \/ rec_term d a hd (S n) = false).
cut (rec_list_terms d la tl (S n) = true \/ rec_list_terms d la tl (S n) = false).
intros.
elim H2.
left.
assumption.
elim H1.
elim H0.
intros.
right.
split; assumption.
simpl in H.
intros.
simpl in H.
simpl in H3.
simpl in H4.
simpl in H5.
rewrite H3 in H.
rewrite H4 in H.
rewrite H5 in H.
simpl in H.
discriminate H.
intros.
simpl in H.
simpl in H2.
simpl in H3.
simpl in H4.
rewrite H3 in H.
rewrite H4 in H.
simpl in H.
discriminate H.
exact (bool_is_true_or_false (rec_list_terms d la tl (S n))).
exact (bool_is_true_or_false (rec_term d a hd (S n))).
Admitted.

Lemma invar_2_2 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list) (n : nat), rec_list_terms d ls (tcons hd tl) n = true \/ rec_term d a hd n = true /\ rec_list_terms d la tl n = true -> rec_list_terms d (prec_cons a la ls) (tcons hd tl) (S n) = true.
Proof.
intros.
elim H.
intro.
simpl in |- *.
simpl in H0.
rewrite H0.
simpl in |- *.
trivial.
intro.
elim H0.
intro.
intro.
simpl in |- *.
simpl in H1.
rewrite H1.
rewrite H2.
simpl in |- *.
Admitted.

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
Admitted.

Lemma invar : forall t : term, invar_term t.
Proof.
Admitted.

Lemma invarl : forall tl : term_list, invar_list tl.
Proof.
Admitted.

Lemma semantic_equiv_0 : forall (d : preDTA) (a : ad) (t : term) (n : nat), rec_term d a t n = true -> reconnaissance d a t.
Proof.
cut (forall t : term, sem_equiv_prop_t t).
intros.
unfold sem_equiv_prop_t in H; intros.
exact (H t d a n H0).
exact (term_term_list_ind sem_equiv_prop_t sem_equiv_prop_l semantic_equiv_0_5 semantic_equiv_0_1 semantic_equiv_0_7).
