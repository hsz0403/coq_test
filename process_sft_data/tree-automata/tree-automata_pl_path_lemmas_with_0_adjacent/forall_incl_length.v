Require Import Arith.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import signature.
Inductive pl_path : Set := | pl_path_nil : pl_path | pl_path_cons : ad -> pl_path -> pl_path.
Inductive pl_path_incl : pl_path -> prec_list -> Prop := | pl_path_incl_nil : pl_path_incl pl_path_nil prec_empty | pl_path_incl_cons : forall (plp : pl_path) (a : ad) (la ls : prec_list), pl_path_incl plp la -> pl_path_incl (pl_path_cons a plp) (prec_cons a la ls) | pl_path_incl_next : forall (plp : pl_path) (a : ad) (la ls : prec_list), pl_path_incl plp ls -> plp <> pl_path_nil -> pl_path_incl plp (prec_cons a la ls).
Inductive pl_path_recon : preDTA -> term_list -> pl_path -> Prop := | pl_path_rec_nil : forall d : preDTA, pl_path_recon d tnil pl_path_nil | pl_path_rec_cons : forall (d : preDTA) (a : ad) (t : term) (plp : pl_path) (tl : term_list), reconnaissance d a t -> pl_path_recon d tl plp -> pl_path_recon d (tcons t tl) (pl_path_cons a plp).
Definition pl_path_rec_equiv_0_def (d : preDTA) (pl : prec_list) (tl : term_list) := liste_reconnait d pl tl -> exists plp : pl_path, pl_path_incl plp pl /\ pl_path_recon d tl plp.
Fixpoint pl_path_length (plp : pl_path) : nat := match plp with | pl_path_nil => 0 | pl_path_cons _ p => S (pl_path_length p) end.
Definition pl_path_rec_equiv_1_def (plp : pl_path) (pl : prec_list) := pl_path_incl plp pl -> forall (d : preDTA) (tl : term_list) (n : nat), pl_path_recon d tl plp -> pl_tl_length pl n -> liste_reconnait d pl tl.
Definition liste_rec_length_def (d : preDTA) (pl : prec_list) (tl : term_list) : Prop := forall n : nat, liste_reconnait d pl tl -> pl_tl_length pl n -> n = lst_length tl.
Definition pl_path_incl_length_def (plp : pl_path) (pl : prec_list) : Prop := forall n : nat, pl_path_incl plp pl -> pl_tl_length pl n -> pl_path_length plp = n.

Lemma forall_incl_length : forall (pl : prec_list) (n : nat), (forall p : pl_path, pl_path_incl p pl -> pl_path_length p = n) -> pl_tl_length pl n.
Proof.
simple induction pl.
intros.
elim (nat_sum n); intros.
rewrite H2 in H1.
elim (non_empty_pl_path_exists (prec_cons a p p0)).
intros.
elim (le_Sn_O 0).
elim H3.
intros.
rewrite (H1 x H4) in H5.
exact H5.
intro.
inversion H3.
elim H2.
intros.
rewrite H3.
rewrite H3 in H1.
elim (pl_sum p0); intros.
rewrite H4.
apply (pl_tl_S a p x).
apply (H x).
intros.
apply (Sn_eq_Sm_n_eq_m (pl_path_length p1) x).
replace (S (pl_path_length p1)) with (pl_path_length (pl_path_cons a p1)).
apply (H1 (pl_path_cons a p1)).
exact (pl_path_incl_cons p1 a p p0 H5).
reflexivity.
apply (pl_tl_propag a p p0 x).
apply (H x).
intros.
cut (pl_path_length (pl_path_cons a p1) = S x).
intros.
simpl in H6.
inversion H6.
reflexivity.
exact (H1 (pl_path_cons a p1) (pl_path_incl_cons p1 a p p0 H5)).
apply (H0 (S x)).
intros.
apply (H1 p1).
apply (pl_path_incl_next p1 a p p0 H5).
intro.
rewrite H6 in H5.
elim H4.
intros.
elim H7.
intros.
elim H8.
intros.
rewrite H9 in H5.
inversion H5.
exact (H15 (refl_equal _)).
intros.
induction n as [| n Hrecn].
exact pl_tl_O.
elim (pl_path_exists prec_empty).
intros.
cut (S n = 0).
intros.
inversion H1.
transitivity (pl_path_length x).
symmetry in |- *.
exact (H x H0).
inversion H0.
reflexivity.
