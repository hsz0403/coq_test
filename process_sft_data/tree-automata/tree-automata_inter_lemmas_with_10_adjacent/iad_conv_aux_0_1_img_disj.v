Require Import Arith.
Require Import NArith Ndec.
Require Import ZArith.
Require Import Bool.
From IntMap Require Import Allmaps.
Require Import bases.
Require Import defs.
Require Import semantics.
Require Import pl_path.
Require Import signature.
Fixpoint iad_conv_aux_0 (p : positive) : positive := match p with | xH => 2%positive | xO p' => xO (xO (iad_conv_aux_0 p')) | xI p' => xO (xI (iad_conv_aux_0 p')) end.
Fixpoint iad_conv_aux_1 (p : positive) : positive := match p with | xH => 1%positive | xO p' => xO (xO (iad_conv_aux_1 p')) | xI p' => xI (xO (iad_conv_aux_1 p')) end.
Fixpoint iad_conv_aux_2 (p0 p1 : positive) {struct p1} : positive := match p0, p1 with | xH, xH => 3%positive | xH, xO p1' => xI (xO (iad_conv_aux_0 p1')) | xH, xI p1' => xI (xI (iad_conv_aux_0 p1')) | xO p0', xH => xO (xI (iad_conv_aux_1 p0')) | xO p0', xO p1' => xO (xO (iad_conv_aux_2 p0' p1')) | xO p0', xI p1' => xO (xI (iad_conv_aux_2 p0' p1')) | xI p0', xH => xI (xI (iad_conv_aux_1 p0')) | xI p0', xO p1' => xI (xO (iad_conv_aux_2 p0' p1')) | xI p0', xI p1' => xI (xI (iad_conv_aux_2 p0' p1')) end.
Definition iad_conv (a0 a1 : ad) : ad := match a0, a1 with | N0, N0 => N0 | N0, Npos p1 => Npos (iad_conv_aux_0 p1) | Npos p0, N0 => Npos (iad_conv_aux_1 p0) | Npos p0, Npos p1 => Npos (iad_conv_aux_2 p0 p1) end.
Definition iad_conv_prop (p : positive) : Prop := (exists q : positive, p = iad_conv_aux_0 q) \/ (exists q : positive, p = iad_conv_aux_1 q) \/ (exists q : positive, (exists r : positive, p = iad_conv_aux_2 q r)).
Inductive ad_couple : Set := cpla : ad -> ad -> ad_couple.
Fixpoint iad_conv_inv_0 (p : positive) : ad_couple := match p with | xH => cpla (Npos 1) N0 | xO xH => cpla N0 (Npos 1) | xI xH => cpla (Npos 1) (Npos 1) | xO (xO p') => match iad_conv_inv_0 p' with | cpla N0 N0 => cpla N0 N0 | cpla N0 (Npos p1) => cpla N0 (Npos (xO p1)) | cpla (Npos p0) N0 => cpla (Npos (xO p0)) N0 | cpla (Npos p0) (Npos p1) => cpla (Npos (xO p0)) (Npos (xO p1)) end | xO (xI p') => match iad_conv_inv_0 p' with | cpla N0 N0 => cpla N0 (Npos 1) | cpla N0 (Npos p1) => cpla N0 (Npos (xI p1)) | cpla (Npos p0) N0 => cpla (Npos (xO p0)) (Npos 1) | cpla (Npos p0) (Npos p1) => cpla (Npos (xO p0)) (Npos (xI p1)) end | xI (xO p') => match iad_conv_inv_0 p' with | cpla N0 N0 => cpla (Npos 1) N0 | cpla N0 (Npos p1) => cpla (Npos 1) (Npos (xO p1)) | cpla (Npos p0) N0 => cpla (Npos (xI p0)) N0 | cpla (Npos p0) (Npos p1) => cpla (Npos (xI p0)) (Npos (xO p1)) end | xI (xI p') => match iad_conv_inv_0 p' with | cpla N0 N0 => cpla (Npos 1) (Npos 1) | cpla N0 (Npos p1) => cpla (Npos 1) (Npos (xI p1)) | cpla (Npos p0) N0 => cpla (Npos (xI p0)) (Npos 1) | cpla (Npos p0) (Npos p1) => cpla (Npos (xI p0)) (Npos (xI p1)) end end.
Definition iad_conv_inv (a : ad) : ad_couple := match a with | N0 => cpla N0 N0 | Npos p => iad_conv_inv_0 p end.
Fixpoint pl_produit_0 (a : ad) (la pl : prec_list) (n : nat) {struct n} : prec_list -> prec_list := fun l : prec_list => match n with | O => prec_empty | S m => match pl with | prec_empty => l | prec_cons a0 la0 ls0 => prec_cons (iad_conv a a0) (pl_produit_1 la m la0) (pl_produit_0 a la ls0 m l) end end with pl_produit_1 (pl0 : prec_list) (n : nat) {struct n} : prec_list -> prec_list := fun pl1 : prec_list => match n with | O => prec_empty | S m => match pl0, pl1 with | prec_empty, prec_empty => prec_empty | prec_empty, prec_cons a1 la1 ls1 => prec_empty | prec_cons a0 la0 ls0, prec_empty => prec_empty | prec_cons a0 la0 ls0, prec_cons a1 la1 ls1 => pl_produit_0 a0 la0 (prec_cons a1 la1 ls1) m (pl_produit_1 ls0 m (prec_cons a1 la1 ls1)) end end.
Fixpoint pl_card (pl : prec_list) : nat := match pl with | prec_empty => 1 | prec_cons a la ls => S (pl_card la + pl_card ls) end.
Definition pl_essence (pl0 pl1 : prec_list) : nat := pl_card pl0 + pl_card pl1.
Definition pl_produit (pl0 pl1 : prec_list) : prec_list := pl_produit_1 pl0 (pl_essence pl0 pl1) pl1.
Fixpoint pl_prof (pl : prec_list) : nat := match pl with | prec_empty => 0 | prec_cons a la ls => S (max (pl_prof la) (pl_prof ls)) end.
Definition pl_produit_0_incr (p0 p1 : prec_list) : Prop := forall (a : ad) (l : prec_list) (n : nat), pl_essence p0 p1 <= n -> pl_produit_0 a p0 p1 (pl_essence p0 p1) l = pl_produit_0 a p0 p1 n l.
Definition pl_produit_1_incr (p0 p1 : prec_list) : Prop := forall n : nat, pl_essence p0 p1 <= n -> pl_produit_1 p0 (pl_essence p0 p1) p1 = pl_produit_1 p0 n p1.
Definition pl_tl_length_prod_def_0 (pl0 pl1 : prec_list) : Prop := forall (l : prec_list) (a : ad) (n m : nat), pl_essence pl0 pl1 <= m -> pl_tl_length pl0 n -> pl_tl_length l (S n) \/ l = prec_empty -> (pl_tl_length pl1 (S n) -> pl_tl_length (pl_produit_0 a pl0 pl1 m l) (S n)) /\ (pl1 = prec_empty -> (pl_tl_length l (S n) -> pl_tl_length (pl_produit_0 a pl0 pl1 m l) (S n)) /\ (l = prec_empty -> pl_produit_0 a pl0 pl1 m l = prec_empty)).
Definition pl_tl_length_prod_def_1 (pl0 pl1 : prec_list) : Prop := forall n m : nat, pl_tl_length pl0 n -> pl_tl_length pl1 n -> pl_essence pl0 pl1 <= m -> pl_tl_length (pl_produit_1 pl0 m pl1) n.
Fixpoint pl_path_product (p0 p1 : pl_path) {struct p1} : pl_path := match p0, p1 with | pl_path_nil, pl_path_nil => pl_path_nil | pl_path_nil, pl_path_cons a b => pl_path_nil | pl_path_cons a b, pl_path_nil => pl_path_nil | pl_path_cons a0 b0, pl_path_cons a1 b1 => pl_path_cons (iad_conv a0 a1) (pl_path_product b0 b1) end.
Definition pl_produit_path_incl_def_0 (pl0 pl1 : prec_list) := forall (n m : nat) (plp0 plp1 : pl_path) (a : ad) (l : prec_list), pl_path_incl plp0 (prec_cons a pl0 prec_empty) -> pl_tl_length pl0 n -> pl_path_incl plp1 pl1 -> pl_tl_length pl1 (S n) -> pl_essence pl0 pl1 <= m -> pl_path_incl (pl_path_product plp0 plp1) (pl_produit_0 a pl0 pl1 m l).
Definition pl_produit_path_incl_def_1 (pl0 pl1 : prec_list) := forall (n m : nat) (plp0 plp1 : pl_path), pl_path_incl plp0 pl0 -> pl_tl_length pl0 n -> pl_path_incl plp1 pl1 -> pl_tl_length pl1 n -> pl_essence pl0 pl1 <= m -> pl_path_incl (pl_path_product plp0 plp1) (pl_produit_1 pl0 m pl1).
Definition pl_produit_path_incl_def_2 (pl0 pl1 : prec_list) := forall (n m : nat) (plp : pl_path) (a : ad) (l : prec_list), pl_path_incl plp (pl_produit_0 a pl0 pl1 m l) -> pl_tl_length pl0 n -> pl_tl_length pl1 (S n) -> pl_essence pl0 pl1 <= m -> (exists plp0 : pl_path, (exists plp1 : pl_path, plp = pl_path_product plp0 plp1 /\ pl_path_incl plp0 (prec_cons a pl0 prec_empty) /\ pl_path_incl plp1 pl1)) \/ pl_path_incl plp l.
Definition pl_produit_path_incl_def_3 (pl0 pl1 : prec_list) := forall (n m : nat) (plp : pl_path), pl_path_incl plp (pl_produit_1 pl0 m pl1) -> pl_tl_length pl0 n -> pl_tl_length pl1 n -> pl_essence pl0 pl1 <= m -> exists plp0 : pl_path, (exists plp1 : pl_path, plp = pl_path_product plp0 plp1 /\ pl_path_incl plp0 pl0 /\ pl_path_incl plp1 pl1).
Fixpoint s_produit_l (a : ad) (p : prec_list) (s : state) {struct s} : state := match s with | M0 => M0 prec_list | M1 a' p' => if N.eqb a a' then M1 prec_list a (pl_produit p p') else M0 prec_list | M2 s0 s1 => match a with | N0 => M2 prec_list (s_produit_l N0 p s0) (M0 prec_list) | Npos q => match q with | xH => M2 prec_list (M0 prec_list) (s_produit_l N0 p s1) | xO q' => M2 prec_list (s_produit_l (Npos q') p s0) (M0 prec_list) | xI q' => M2 prec_list (M0 prec_list) (s_produit_l (Npos q') p s1) end end end.
Definition sproductl_0_def (s : state) : Prop := forall (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list), MapGet prec_list (M1 prec_list a p) c = Some r0 -> MapGet prec_list s c = Some r1 -> MapGet prec_list (s_produit_l a p s) c = Some (pl_produit r0 r1).
Definition sproductl_1_def (s : state) : Prop := forall (a : ad) (p : prec_list) (c : ad) (r : prec_list), MapGet prec_list (s_produit_l a p s) c = Some r -> exists r0 : prec_list, (exists r1 : prec_list, MapGet prec_list (M1 prec_list a p) c = Some r0 /\ MapGet prec_list s c = Some r1).
Fixpoint s_produit_r (a : ad) (p : prec_list) (s : state) {struct s} : state := match s with | M0 => M0 prec_list | M1 a' p' => if N.eqb a a' then M1 prec_list a (pl_produit p' p) else M0 prec_list | M2 s0 s1 => match a with | N0 => M2 prec_list (s_produit_r N0 p s0) (M0 prec_list) | Npos q => match q with | xH => M2 prec_list (M0 prec_list) (s_produit_r N0 p s1) | xO q' => M2 prec_list (s_produit_r (Npos q') p s0) (M0 prec_list) | xI q' => M2 prec_list (M0 prec_list) (s_produit_r (Npos q') p s1) end end end.
Definition sproductr_0_def (s : state) : Prop := forall (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list), MapGet prec_list (M1 prec_list a p) c = Some r0 -> MapGet prec_list s c = Some r1 -> MapGet prec_list (s_produit_r a p s) c = Some (pl_produit r1 r0).
Definition sproductr_1_def (s : state) : Prop := forall (a : ad) (p : prec_list) (c : ad) (r : prec_list), MapGet prec_list (s_produit_r a p s) c = Some r -> exists r0 : prec_list, (exists r1 : prec_list, MapGet prec_list (M1 prec_list a p) c = Some r0 /\ MapGet prec_list s c = Some r1).
Fixpoint s_produit (s0 s1 : state) {struct s1} : state := match s0, s1 with | M0, M0 => M0 prec_list | M0, M1 a1 p1 => M0 prec_list | M0, M2 s10 s11 => M0 prec_list | M1 a0 p0, M0 => M0 prec_list | M1 a0 p0, M1 a1 p1 => s_produit_l a0 p0 (M1 prec_list a1 p1) | M1 a0 p0, M2 s10 s11 => s_produit_l a0 p0 (M2 prec_list s10 s11) | M2 s00 s01, M0 => M0 prec_list | M2 s00 s01, M1 a1 p1 => s_produit_r a1 p1 (M2 prec_list s00 s01) | M2 s00 s01, M2 s10 s11 => M2 prec_list (s_produit s00 s10) (s_produit s01 s11) end.
Fixpoint preDTA_produit_l (a : ad) (s : state) (d : preDTA) {struct d} : preDTA := match d with | M0 => M0 state | M1 a' s' => M1 state (iad_conv a a') (s_produit s s') | M2 s0 s1 => match a with | N0 => M2 state (M2 state (preDTA_produit_l N0 s s0) (preDTA_produit_l N0 s s1)) (M0 state) | Npos p => match p with | xH => M2 state (M0 state) (M2 state (preDTA_produit_l N0 s s0) (preDTA_produit_l N0 s s1)) | xO p' => M2 state (M2 state (preDTA_produit_l (Npos p') s s0) (preDTA_produit_l (Npos p') s s1)) (M0 state) | xI p' => M2 state (M0 state) (M2 state (preDTA_produit_l (Npos p') s s0) (preDTA_produit_l (Npos p') s s1)) end end end.
Fixpoint preDTA_produit_r (a : ad) (s : state) (d : preDTA) {struct d} : preDTA := match d with | M0 => M0 state | M1 a' s' => M1 state (iad_conv a' a) (s_produit s' s) | M2 s0 s1 => match a with | N0 => M2 state (M2 state (preDTA_produit_r N0 s s0) (M0 state)) (M2 state (preDTA_produit_r N0 s s1) (M0 state)) | Npos p => match p with | xH => M2 state (M2 state (M0 state) (preDTA_produit_r N0 s s0)) (M2 state (M0 state) (preDTA_produit_r N0 s s1)) | xO p' => M2 state (M2 state (preDTA_produit_r (Npos p') s s0) (M0 state)) (M2 state (preDTA_produit_r (Npos p') s s1) (M0 state)) | xI p' => M2 state (M2 state (M0 state) (preDTA_produit_r (Npos p') s s0)) (M2 state (M0 state) (preDTA_produit_r (Npos p') s s1)) end end end.
Fixpoint preDTA_produit (d0 d1 : preDTA) {struct d1} : preDTA := match d0, d1 with | M0, M0 => M0 state | M0, M1 a1 s1 => M0 state | M0, M2 s10 s11 => M0 state | M1 a0 s0, M0 => M0 state | M1 a0 s0, M1 a1 s1 => preDTA_produit_l a0 s0 (M1 state a1 s1) | M1 a0 s0, M2 s10 s11 => preDTA_produit_l a0 s0 (M2 state s10 s11) | M2 s00 s01, M0 => M0 state | M2 s00 s01, M1 a1 s1 => preDTA_produit_r a1 s1 (M2 state s00 s01) | M2 s00 s01, M2 s10 s11 => M2 state (M2 state (preDTA_produit s00 s10) (preDTA_produit s00 s11)) (M2 state (preDTA_produit s01 s10) (preDTA_produit s01 s11)) end.
Definition predta_produit_0d_def (d : preDTA) : Prop := forall (a : ad) (s : state) (a0 a1 : ad) (s0 s1 : state), MapGet state (M1 state a s) a0 = Some s0 -> MapGet state d a1 = Some s1 -> MapGet state (preDTA_produit_l a s d) (iad_conv a0 a1) = Some (s_produit s0 s1).
Definition predta_produit_1_def (d : preDTA) : Prop := forall (a : ad) (s : state) (a0 a1 : ad) (s0 s1 : state), MapGet state (M1 state a s) a0 = Some s0 -> MapGet state d a1 = Some s1 -> MapGet state (preDTA_produit_r a s d) (iad_conv a1 a0) = Some (s_produit s1 s0).
Definition predta_produit_3_def (d0 : preDTA) : Prop := forall (a a0 : ad) (s s0 : state), MapGet state (preDTA_produit_l a0 s0 d0) a = Some s -> exists a1 : ad, (exists a2 : ad, (exists s1 : state, (exists s2 : state, a = iad_conv a1 a2 /\ MapGet state (M1 state a0 s0) a1 = Some s1 /\ MapGet state d0 a2 = Some s2))).
Definition predta_produit_4_def (d0 : preDTA) : Prop := forall (a a0 : ad) (s s0 : state), MapGet state (preDTA_produit_r a0 s0 d0) a = Some s -> exists a1 : ad, (exists a2 : ad, (exists s1 : state, (exists s2 : state, a = iad_conv a1 a2 /\ MapGet state (M1 state a0 s0) a2 = Some s1 /\ MapGet state d0 a1 = Some s2))).
Definition predta_inter_def_0 (t : term) : Prop := forall (d0 d1 : preDTA) (a0 a1 : ad), predta_compatible d0 d1 -> reconnaissance d0 a0 t -> reconnaissance d1 a1 t -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t.
Definition predta_inter_def_1 (t : term) : Prop := forall (d0 d1 : preDTA) (a0 a1 : ad), predta_compatible d0 d1 -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t -> reconnaissance d0 a0 t /\ reconnaissance d1 a1 t.
Definition inter (d0 d1 : DTA) : DTA := match d0, d1 with | dta p0 a0, dta p1 a1 => dta (preDTA_produit p0 p1) (iad_conv a0 a1) end.

Lemma iad_conv_aux_0_inj : forall p0 p1 : positive, iad_conv_aux_0 p0 = iad_conv_aux_0 p1 -> p0 = p1.
Proof.
simple induction p0.
simple induction p1.
intros.
simpl in H1.
inversion H1.
rewrite (H p2 H3).
trivial.
intros.
simpl in H1.
inversion H1.
intros.
simpl in H0.
inversion H0.
intros.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
simpl in H0.
inversion H0.
simpl in H0.
inversion H0.
rewrite (H p1 H2).
trivial.
inversion H0.
simple induction p1.
intros.
inversion H0.
intros.
inversion H0.
intros.
Admitted.

Lemma iad_conv_aux_1_inj : forall p0 p1 : positive, iad_conv_aux_1 p0 = iad_conv_aux_1 p1 -> p0 = p1.
Proof.
simple induction p0.
simple induction p1.
intros.
simpl in H1.
inversion H1.
rewrite (H p2 H3).
trivial.
intros.
inversion H1.
intros.
inversion H0.
intros.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
inversion H0.
simpl in H0.
inversion H0.
rewrite (H p1 H2).
trivial.
inversion H0.
simple induction p1.
intros.
inversion H0.
intros.
inversion H0.
intros.
Admitted.

Lemma iad_conv_aux_img_disj : forall p0 p1 p2 : positive, iad_conv_aux_0 p0 <> iad_conv_aux_2 p1 p2 /\ iad_conv_aux_1 p0 <> iad_conv_aux_2 p1 p2.
Proof.
simple induction p0.
simple induction p1.
simple induction p3.
intros.
split; intro.
inversion H2.
inversion H2.
intros.
split; intro.
inversion H2.
simpl in H2.
inversion H2.
elim (H p2 p4); intros.
exact (H5 H4).
split; intro.
inversion H1.
inversion H1.
simple induction p3.
intros.
split; intro.
simpl in H2.
inversion H2.
elim (H p2 p4); intros.
exact (H3 H4).
inversion H2.
intros.
split; intro.
inversion H2.
inversion H2.
split; intro.
simpl in H1.
inversion H1.
exact (iad_conv_aux_0_1_img_disj p p2 H3).
inversion H1.
simple induction p2.
intros.
split; intro.
inversion H1.
inversion H1.
intros.
split; intro.
inversion H1.
simpl in H1.
inversion H1.
exact (iad_conv_aux_0_1_img_disj _ _ (sym_equal H3)).
split; intro.
inversion H0.
inversion H0.
intros.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
split; intro.
inversion H0.
inversion H0.
split; intro.
simpl in H0.
inversion H0.
elim (H p1 p2).
intros.
exact (H1 H2).
simpl in H0.
inversion H0.
elim (H p1 p2); intros.
exact (H3 H2).
split; intro.
inversion H0.
inversion H0.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
simple induction p1.
intros.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
intros.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
split; intro.
inversion H0.
inversion H0.
intros.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
split; intro.
inversion H.
inversion H.
split; intro.
inversion H.
inversion H.
split; intro.
inversion H.
Admitted.

Lemma iad_conv_aux_0_2_img_disj : forall p0 p1 p2 : positive, iad_conv_aux_0 p0 <> iad_conv_aux_2 p1 p2.
Proof.
intros.
elim (iad_conv_aux_img_disj p0 p1 p2).
intros.
Admitted.

Lemma iad_conv_aux_1_2_img_disj : forall p0 p1 p2 : positive, iad_conv_aux_1 p0 <> iad_conv_aux_2 p1 p2.
Proof.
intros.
elim (iad_conv_aux_img_disj p0 p1 p2).
intros.
Admitted.

Lemma iad_conv_aux_2_inj : forall p0 p1 p2 p3 : positive, iad_conv_aux_2 p0 p1 = iad_conv_aux_2 p2 p3 -> p0 = p2 /\ p1 = p3.
Proof.
simple induction p0.
intros.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H0.
inversion H0.
elim (H p1 p2 p3).
intros.
rewrite H1.
rewrite H3.
split.
trivial.
trivial.
assumption.
inversion H0.
simpl in H0.
inversion H0.
elim (iad_conv_aux_1_2_img_disj p2 p p1 (sym_equal H2)).
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
inversion H0.
simpl in H0.
inversion H0.
elim (H p1 p2 p3 H2).
intros.
rewrite H1.
rewrite H3.
split; trivial.
inversion H0.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H0.
inversion H0.
elim (iad_conv_aux_1_2_img_disj p p2 p3 H2).
inversion H0.
simpl in H0.
inversion H0.
rewrite (iad_conv_aux_1_inj p p2 H2).
split; trivial.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H0.
inversion H0.
inversion H0.
inversion H0.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
inversion H0.
inversion H0.
inversion H0.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
inversion H0.
inversion H0.
inversion H0.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H0.
inversion H0.
elim (iad_conv_aux_0_2_img_disj p3 p p1 (sym_equal H2)).
inversion H0.
inversion H0.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
inversion H0.
simpl in H0.
inversion H0.
elim (iad_conv_aux_0_2_img_disj p3 p p1 (sym_equal H2)).
inversion H0.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H0.
inversion H0.
elim (iad_conv_aux_0_1_img_disj p3 p (sym_equal H2)).
inversion H0.
inversion H0.
simple induction p1.
intros.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
induction p4 as [p4 Hrecp4| p4 Hrecp4| ].
inversion H1.
inversion H1.
inversion H1.
induction p4 as [p4 Hrecp4| p4 Hrecp4| ].
simpl in H1.
inversion H1.
elim (H p2 p3 p4 H3).
intros.
rewrite H2.
rewrite H4.
split; trivial.
inversion H1.
simpl in H1.
inversion H1.
elim (iad_conv_aux_1_2_img_disj p3 p p2 (sym_equal H3)).
induction p4 as [p4 Hrecp4| p4 Hrecp4| ].
inversion H1.
inversion H1.
inversion H1.
intros.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
induction p4 as [p4 Hrecp4| p4 Hrecp4| ].
inversion H1.
inversion H1.
inversion H1.
induction p4 as [p4 Hrecp4| p4 Hrecp4| ].
inversion H1.
simpl in H1.
inversion H1.
elim (H p2 p3 p4 H3).
intros.
rewrite H2.
rewrite H4.
split; trivial.
inversion H1.
induction p4 as [p4 Hrecp4| p4 Hrecp4| ]; inversion H1.
intros.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
inversion H0.
inversion H0.
inversion H0.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H0.
inversion H0.
elim (iad_conv_aux_1_2_img_disj p p2 p3 H2).
inversion H0.
simpl in H0.
inversion H0.
rewrite (iad_conv_aux_1_inj _ _ H2).
split; trivial.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H0.
intros.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H.
inversion H.
elim (iad_conv_aux_0_2_img_disj _ _ _ H1).
inversion H.
simpl in H.
inversion H.
elim (iad_conv_aux_0_1_img_disj _ _ H1).
induction p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H.
inversion H.
rewrite (iad_conv_aux_0_inj _ _ H1).
split; trivial.
inversion H.
simpl in H.
inversion H.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
inversion H.
simpl in H.
inversion H.
elim (iad_conv_aux_0_2_img_disj _ _ _ H1).
inversion H.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
inversion H.
simpl in H.
inversion H.
rewrite (iad_conv_aux_0_inj _ _ H1).
split; trivial.
inversion H.
induction p2 as [p2 Hrecp2| p2 Hrecp2| ].
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H.
inversion H.
inversion H.
simpl in H.
inversion H.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ]; inversion H.
induction p3 as [p3 Hrecp3| p3 Hrecp3| ].
simpl in H.
inversion H.
inversion H.
Admitted.

Lemma iad_conv_inj : forall a0 a1 a2 a3 : ad, iad_conv a0 a1 = iad_conv a2 a3 -> a0 = a2 /\ a1 = a3.
Proof.
simple induction a0; simple induction a1; simple induction a2; simple induction a3; intros.
split; trivial.
inversion H.
inversion H.
inversion H.
inversion H.
simpl in H.
inversion H.
rewrite (iad_conv_aux_0_inj _ _ H1).
split; trivial.
simpl in H.
inversion H.
elim (iad_conv_aux_0_1_img_disj _ _ H1).
simpl in H.
inversion H.
elim (iad_conv_aux_0_2_img_disj _ _ _ H1).
inversion H.
simpl in H.
inversion H.
elim (iad_conv_aux_0_1_img_disj _ _ (sym_equal H1)).
simpl in H.
inversion H.
rewrite (iad_conv_aux_1_inj _ _ H1).
split; trivial.
simpl in H.
inversion H.
elim (iad_conv_aux_1_2_img_disj _ _ _ H1).
inversion H.
simpl in H.
inversion H.
elim (iad_conv_aux_0_2_img_disj _ _ _ (sym_equal H1)).
simpl in H.
inversion H.
elim (iad_conv_aux_1_2_img_disj _ _ _ (sym_equal H1)).
simpl in H.
inversion H.
elim (iad_conv_aux_2_inj _ _ _ _ H1).
intros.
rewrite H0.
rewrite H2.
Admitted.

Lemma iad_conv_surj_0 : forall p : positive, iad_conv_prop p -> iad_conv_prop (xO (xO p)).
Proof.
intros.
elim H.
intro.
elim H0.
intros.
left.
split with (xO x).
simpl in |- *.
rewrite <- H1.
trivial.
intros.
elim H0.
intros.
elim H1.
intros.
right.
left.
split with (xO x).
simpl in |- *.
rewrite <- H2.
trivial.
intro.
elim H1.
intros.
elim H2.
intros.
right.
right.
split with (xO x).
split with (xO x0).
simpl in |- *.
rewrite <- H3.
Admitted.

Lemma iad_conv_surj_1 : forall p : positive, iad_conv_prop p -> iad_conv_prop (xO (xI p)).
intros.
elim H; intros.
elim H0.
intros.
left.
split with (xI x).
simpl in |- *.
rewrite <- H1.
trivial.
elim H0; intros.
elim H1.
intros.
right.
right.
split with (xO x).
split with 1%positive.
simpl in |- *.
rewrite H2.
trivial.
elim H1.
intros.
elim H2.
intros.
right.
right.
split with (xO x).
split with (xI x0).
simpl in |- *.
rewrite H3.
Admitted.

Lemma iad_conv_surj_2 : forall p : positive, iad_conv_prop p -> iad_conv_prop (xI (xO p)).
Proof.
intros.
elim H; intros.
elim H0.
intros.
right.
right.
split with 1%positive.
split with (xO x).
simpl in |- *.
rewrite H1.
trivial.
elim H0; intros.
right.
left.
elim H1.
intros.
split with (xI x).
simpl in |- *.
rewrite H2.
trivial.
elim H1.
intros.
elim H2.
intros.
right.
right.
split with (xI x).
split with (xO x0).
simpl in |- *.
rewrite H3.
Admitted.

Lemma iad_conv_surj_3 : forall p : positive, iad_conv_prop p -> iad_conv_prop (xI (xI p)).
Proof.
intros.
elim H; intros.
elim H0.
intros.
right.
right.
split with 1%positive.
split with (xI x).
simpl in |- *.
rewrite H1.
trivial.
elim H0; intros.
right.
right.
elim H1.
intros.
split with (xI x).
split with 1%positive.
simpl in |- *.
rewrite H2.
trivial.
elim H1.
intros.
elim H2.
intros.
right.
right.
split with (xI x).
split with (xI x0).
simpl in |- *.
rewrite H3.
Admitted.

Lemma iad_conv_surj_4 : forall p : positive, iad_conv_prop p /\ iad_conv_prop (xO p) /\ iad_conv_prop (xI p).
Proof.
simple induction p.
intros.
elim H.
intros.
elim H1.
intros.
split.
exact H3.
split.
exact (iad_conv_surj_1 p0 H0).
exact (iad_conv_surj_3 p0 H0).
intros.
elim H.
intros.
elim H1.
intros.
split.
exact H2.
split.
exact (iad_conv_surj_0 p0 H0).
exact (iad_conv_surj_2 p0 H0).
split.
right.
left.
split with 1%positive.
trivial.
split.
left.
split with 1%positive.
reflexivity.
right.
right.
split with 1%positive.
split with 1%positive.
Admitted.

Lemma iad_conv_aux_0_1_img_disj : forall p0 p1 : positive, iad_conv_aux_0 p0 <> iad_conv_aux_1 p1.
Proof.
simple induction p0.
simple induction p1.
intros.
intro.
simpl in H1.
inversion H1.
intros.
intro.
inversion H1.
intro.
inversion H0.
intros.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
intro.
inversion H0.
intro.
unfold iad_conv_aux_0 in H0.
unfold iad_conv_aux_1 in H0.
inversion H0.
exact (H p1 H2).
intro.
inversion H0.
simple induction p1.
intros.
intro.
inversion H0.
intros.
intro.
inversion H0.
intro.
inversion H.
