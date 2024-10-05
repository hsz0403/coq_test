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

Lemma liste_rec_length_2 : forall (d : preDTA) (a : ad) (la ls : prec_list) (hd : term) (tl : term_list), liste_reconnait d ls (tcons hd tl) -> liste_rec_length_def d ls (tcons hd tl) -> liste_rec_length_def d (prec_cons a la ls) (tcons hd tl).
Proof.
unfold liste_rec_length_def in |- *.
intros.
simpl in |- *.
induction n as [| n Hrecn].
inversion H2.
simpl in H0.
inversion H2.
rewrite <- H6 in H.
inversion H.
rewrite <- (H0 (S n) H H8).
reflexivity.
