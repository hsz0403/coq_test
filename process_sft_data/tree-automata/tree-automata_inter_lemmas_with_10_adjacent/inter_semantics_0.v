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

Lemma predta_produit_4 : forall (d0 : preDTA) (a a0 : ad) (s s0 : state), MapGet state (preDTA_produit_r a0 s0 d0) a = Some s -> exists a1 : ad, (exists a2 : ad, (exists s1 : state, (exists s2 : state, a = iad_conv a1 a2 /\ MapGet state (M1 state a0 s0) a2 = Some s1 /\ MapGet state d0 a1 = Some s2))).
Proof.
Admitted.

Lemma predta_produit_5 : forall (d0 d1 : preDTA) (a : ad) (s : state), MapGet state (preDTA_produit d0 d1) a = Some s -> exists a0 : ad, (exists a1 : ad, (exists s0 : state, (exists s1 : state, a = iad_conv a0 a1 /\ MapGet state d0 a0 = Some s0 /\ MapGet state d1 a1 = Some s1))).
Proof.
simple induction d0.
intros.
induction d1 as [| a0 a1| d1_1 Hrecd1_1 d1_0 Hrecd1_0]; inversion H.
intros.
induction d1 as [| a2 a3| d1_1 Hrecd1_1 d1_0 Hrecd1_0].
simpl in H.
inversion H.
cut (preDTA_produit (M1 state a a0) (M1 state a2 a3) = preDTA_produit_l a a0 (M1 state a2 a3)).
intro.
rewrite H0 in H.
exact (predta_produit_3 (M1 state a2 a3) a1 a s a0 H).
reflexivity.
cut (preDTA_produit (M1 state a a0) (M2 state d1_1 d1_0) = preDTA_produit_l a a0 (M2 state d1_1 d1_0)).
intro.
rewrite H0 in H.
exact (predta_produit_3 (M2 state d1_1 d1_0) a1 a s a0 H).
reflexivity.
simple induction d1.
intros.
inversion H1.
intros.
cut (preDTA_produit (M2 state m m0) (M1 state a a0) = preDTA_produit_r a a0 (M2 state m m0)).
intro.
rewrite H2 in H1.
elim (predta_produit_4 (M2 state m m0) a1 a s a0 H1).
intros.
elim H3.
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H8.
intros.
split with x.
split with x0.
split with x2.
split with x1.
split.
assumption.
split; assumption.
reflexivity.
intros.
clear H1.
clear H2.
induction a as [| p].
simpl in H3.
elim (H m1 N0 s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
split with N0.
split with N0.
simpl in |- *.
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 _ _ H6); intros.
rewrite <- H10 in H8.
rewrite <- H11 in H9.
split.
reflexivity.
split.
exact H8.
exact H9.
induction p as [p Hrecp| p Hrecp| ].
clear Hrecp.
induction p as [p Hrecp| p Hrecp| ].
clear Hrecp.
simpl in H3.
elim (H0 m2 (Npos p) s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
induction x as [| p0].
induction x0 as [| p0].
inversion H6.
split with (Npos 1).
split with (Npos (xI p0)).
split with x1.
split with x2.
split.
simpl in |- *.
simpl in H6.
inversion H6.
reflexivity.
simpl in |- *.
split; assumption.
induction x0 as [| p1].
split with (Npos (xI p0)).
split with (Npos 1).
split with x1.
split with x2.
simpl in |- *.
split.
simpl in H6.
inversion H6.
reflexivity.
split; assumption.
split with (Npos (xI p0)).
split with (Npos (xI p1)).
split with x1.
split with x2.
simpl in |- *.
simpl in H6.
inversion H6.
split.
reflexivity.
split; assumption.
clear Hrecp.
simpl in H3.
elim (H0 m1 (Npos p) s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
induction x as [| p0].
induction x0 as [| p0].
inversion H6.
split with (Npos 1).
split with (Npos (xO p0)).
split with x1.
split with x2.
simpl in H6.
inversion H6.
simpl in |- *.
split.
reflexivity.
split; assumption.
induction x0 as [| p1].
split with (Npos (xI p0)).
split with N0.
split with x1.
split with x2.
simpl in H6.
inversion H6.
simpl in |- *.
split.
reflexivity.
split; assumption.
split with (Npos (xI p0)).
split with (Npos (xO p1)).
split with x1.
split with x2.
simpl in H6.
inversion H6.
split.
reflexivity.
split; assumption.
simpl in H3.
elim (H0 m2 N0 s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
induction x as [| p].
induction x0 as [| p].
split with (Npos 1).
split with (Npos 1).
split with x1.
split with x2.
simpl in |- *.
split.
reflexivity.
split; assumption.
simpl in H6.
inversion H6.
induction x0 as [| p0]; simpl in H6; inversion H6.
clear Hrecp.
induction p as [p Hrecp| p Hrecp| ].
clear Hrecp.
simpl in H3.
elim (H m2 (Npos p) s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
induction x as [| p0].
induction x0 as [| p0].
simpl in H6.
inversion H6.
split with N0.
split with (Npos (xI p0)).
split with x1.
split with x2.
simpl in H6.
inversion H6.
simpl in |- *.
split.
reflexivity.
split; assumption.
induction x0 as [| p1].
split with (Npos (xO p0)).
split with (Npos 1).
split with x1.
split with x2.
simpl in H6.
inversion H6.
simpl in |- *.
split.
reflexivity.
split; assumption.
split with (Npos (xO p0)).
split with (Npos (xI p1)).
split with x1.
split with x2.
simpl in H6.
inversion H6.
simpl in |- *.
split.
reflexivity.
split; assumption.
clear Hrecp.
simpl in H3.
elim (H m1 (Npos p) s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
induction x as [| p0].
induction x0 as [| p0].
simpl in H6.
inversion H6.
split with N0.
split with (Npos (xO p0)).
split with x1.
split with x2.
simpl in H6.
inversion H6.
simpl in |- *.
split.
reflexivity.
split; assumption.
induction x0 as [| p1].
simpl in H6.
split with (Npos (xO p0)).
split with N0.
split with x1.
split with x2.
simpl in H6.
inversion H6.
split.
reflexivity.
split; assumption.
split with (Npos (xO p0)).
split with (Npos (xO p1)).
split with x1.
split with x2.
simpl in H6.
inversion H6.
simpl in |- *.
split.
reflexivity.
split; assumption.
simpl in H3.
elim (H m2 N0 s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
induction x as [| p].
induction x0 as [| p].
split with N0.
split with (Npos 1).
split with x1.
split with x2.
simpl in |- *.
split.
reflexivity.
split; assumption.
simpl in H6.
inversion H6.
induction x0 as [| p0].
simpl in H6.
inversion H6.
simpl in H6.
inversion H6.
simpl in H3.
elim (H0 m1 N0 s H3).
intros.
elim H1.
intros.
elim H2.
intros.
elim H4.
intros.
elim H5.
intros.
elim H7.
intros.
split with (Npos 1).
split with N0.
split with x1.
split with x2.
simpl in |- *.
split.
reflexivity.
elim (iad_conv_inj N0 N0 _ _ H6).
intros.
rewrite <- H10 in H8.
rewrite <- H11 in H9.
Admitted.

Lemma pl_produit_rec_0 : forall tl : term_list, (forall u : term, term_list_occur u tl -> forall (d0 d1 : preDTA) (a0 a1 : ad), predta_compatible d0 d1 -> reconnaissance d0 a0 u -> reconnaissance d1 a1 u -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u) -> forall (d0 d1 : preDTA) (plp0 plp1 : pl_path), predta_compatible d0 d1 -> pl_path_recon d0 tl plp0 -> pl_path_recon d1 tl plp1 -> pl_path_recon (preDTA_produit d0 d1) tl (pl_path_product plp0 plp1).
Proof.
simple induction tl.
intros.
inversion H1.
inversion H2.
simpl in |- *.
exact (pl_path_rec_nil (preDTA_produit d0 d1)).
intros.
inversion H2.
inversion H3.
simpl in |- *.
apply (pl_path_rec_cons (preDTA_produit d0 d1) (iad_conv a a0) t (pl_path_product plp plp2) t0).
exact (H0 t (tlo_head t t t0 (to_eq t)) d0 d1 a a0 H1 H7 H13).
Admitted.

Lemma pl_produit_rec_1 : forall (d0 d1 : preDTA) (tl : term_list) (pl0 pl1 : prec_list), liste_reconnait d0 pl0 tl -> liste_reconnait d1 pl1 tl -> pl_tl_length pl0 (lst_length tl) -> pl_tl_length pl1 (lst_length tl) -> predta_compatible d0 d1 -> (forall u : term, term_list_occur u tl -> forall (d0 d1 : preDTA) (a0 a1 : ad), predta_compatible d0 d1 -> reconnaissance d0 a0 u -> reconnaissance d1 a1 u -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u) -> liste_reconnait (preDTA_produit d0 d1) (pl_produit pl0 pl1) tl.
Proof.
intros.
elim (pl_path_rec_equiv_0 d0 pl0 tl H).
elim (pl_path_rec_equiv_0 d1 pl1 tl H0).
intros.
cut (pl_path_incl (pl_path_product x0 x) (pl_produit pl0 pl1)).
intro.
elim H5.
intros.
elim H6.
intros.
apply (pl_path_rec_equiv_1 (pl_path_product x0 x) (pl_produit pl0 pl1) H7 (preDTA_produit d0 d1) tl (lst_length tl)).
exact (pl_produit_rec_0 tl H4 d0 d1 x0 x H3 H11 H9).
apply (pl_tl_length_prod pl0 pl1 (lst_length tl)).
exact H1.
exact H2.
elim H5.
intros.
elim H6.
intros.
Admitted.

Lemma pl_produit_rec_2 : forall tl : term_list, (forall u : term, term_list_occur u tl -> forall (d0 d1 : preDTA) (a0 a1 : ad), predta_compatible d0 d1 -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u -> reconnaissance d0 a0 u /\ reconnaissance d1 a1 u) -> forall (d0 d1 : preDTA) (plp : pl_path), predta_compatible d0 d1 -> pl_path_recon (preDTA_produit d0 d1) tl plp -> exists plp0 : pl_path, (exists plp1 : pl_path, plp = pl_path_product plp0 plp1 /\ pl_path_recon d0 tl plp0 /\ pl_path_recon d1 tl plp1).
Proof.
simple induction tl.
intros.
inversion H1.
split with pl_path_nil.
split with pl_path_nil.
simpl in |- *.
split.
reflexivity.
split.
exact (pl_path_rec_nil d0).
exact (pl_path_rec_nil d1).
intros.
inversion H2.
elim (H (fun (u : term) (pr : term_list_occur u t0) => H0 u (tlo_tail u t t0 pr)) d0 d1 plp0 H1 H8).
intros.
elim H9.
intros.
elim (iad_conv_surj a).
intros.
elim H11.
intros.
rewrite H12 in H6.
elim (H0 t (tlo_head t t t0 (to_eq t)) d0 d1 x1 x2 H1 H6).
intros.
split with (pl_path_cons x1 x).
split with (pl_path_cons x2 x0).
simpl in |- *.
split.
rewrite H12.
elim H10.
intros.
rewrite H15.
reflexivity.
elim H10.
intros.
elim H16.
intros.
split.
exact (pl_path_rec_cons d0 x1 t x t0 H13 H17).
Admitted.

Lemma pl_produit_rec_3 : forall (d0 d1 : preDTA) (tl : term_list) (pl0 pl1 : prec_list) (n : nat), liste_reconnait (preDTA_produit d0 d1) (pl_produit pl0 pl1) tl -> predta_compatible d0 d1 -> pl_tl_length pl0 n -> pl_tl_length pl1 n -> (forall u : term, term_list_occur u tl -> forall (d0 d1 : preDTA) (a0 a1 : ad), predta_compatible d0 d1 -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) u -> reconnaissance d0 a0 u /\ reconnaissance d1 a1 u) -> liste_reconnait d0 pl0 tl /\ liste_reconnait d1 pl1 tl.
Proof.
intros.
elim (pl_path_rec_equiv_0 (preDTA_produit d0 d1) (pl_produit pl0 pl1) tl H).
intros.
elim H4.
intros.
elim (pl_produit_rec_2 tl H3 d0 d1 x H0 H6).
intros.
elim H7.
intros.
elim H8.
intros.
elim H10.
intros.
elim (pl_produit_path_incl_4 pl0 pl1 n x H5 H1 H2).
intros.
elim H13.
intros.
elim H14.
intros.
elim H16.
intros.
elim (pl_produit_path_incl_inj x0 x1 x2 x3 n).
intros.
rewrite <- H19 in H17.
rewrite <- H20 in H18.
split.
exact (pl_path_rec_equiv_1 x0 pl0 H17 d0 tl n H11 H1).
exact (pl_path_rec_equiv_1 x1 pl1 H18 d1 tl n H12 H2).
transitivity (lst_length tl).
exact (pl_path_rec_length x0 tl d0 H11).
symmetry in |- *.
exact (liste_rec_length (pl_produit pl0 pl1) tl (preDTA_produit d0 d1) n H (pl_tl_length_prod pl0 pl1 n H1 H2)).
transitivity (lst_length tl).
exact (pl_path_rec_length x1 tl d1 H12).
symmetry in |- *.
exact (liste_rec_length (pl_produit pl0 pl1) tl (preDTA_produit d0 d1) n H (pl_tl_length_prod pl0 pl1 n H1 H2)).
exact (pl_path_incl_length x2 pl0 n H17 H1).
exact (pl_path_incl_length x3 pl1 n H18 H2).
transitivity x.
symmetry in |- *.
exact H9.
Admitted.

Lemma predta_inter_0 : forall (a : ad) (tl : term_list), (forall u : term, term_list_occur u tl -> predta_inter_def_0 u) -> predta_inter_def_0 (app a tl).
Proof.
unfold predta_inter_def_0 in |- *.
intros.
inversion H1.
inversion H2.
inversion H4.
inversion H9.
apply (rec_dta (preDTA_produit d0 d1) (iad_conv a0 a1) (app a tl) (s_produit ladj ladj0)).
exact (predta_produit_2 d0 d1 a0 a1 ladj ladj0 H3 H8).
apply (rec_st (preDTA_produit d0 d1) (s_produit ladj ladj0) a tl (pl_produit l l0)).
exact (s_produit_0 ladj ladj0 a l l0 H17 H23).
apply (pl_produit_rec_1 d0 d1 tl l l0 H18 H24).
cut (pl_compatible l l0).
intro.
elim H25.
intros.
elim H26.
intros.
rewrite <- (liste_rec_length l tl d0 x H18 H27).
exact H27.
cut (st_compatible ladj ladj0).
intro.
exact (H25 a l l0 H17 H23).
apply (H0 ladj ladj0).
split with a0.
exact H3.
split with a1.
exact H8.
cut (pl_compatible l l0).
intro.
elim H25.
intros.
elim H26.
intros.
rewrite <- (liste_rec_length l0 tl d1 x H24 H28).
exact H28.
cut (st_compatible ladj ladj0).
intro.
exact (H25 a l l0 H17 H23).
apply (H0 ladj ladj0).
split with a0.
exact H3.
split with a1.
exact H8.
exact H0.
Admitted.

Lemma predta_inter_1 : forall (a : ad) (tl : term_list), (forall u : term, term_list_occur u tl -> predta_inter_def_1 u) -> predta_inter_def_1 (app a tl).
Proof.
unfold predta_inter_def_1 in |- *.
intros.
inversion H1.
inversion H3.
elim (predta_produit_5 d0 d1 (iad_conv a0 a1) ladj H2).
intros.
elim H13.
intros.
elim H14.
intros.
elim H15.
intros.
elim H16.
intros.
elim H18.
intros.
elim (iad_conv_inj _ _ _ _ H17).
intros.
rewrite <- H21 in H19.
rewrite <- H22 in H20.
rewrite (predta_produit_2 d0 d1 a0 a1 x1 x2 H19 H20) in H2.
inversion H2.
rewrite <- H24 in H11.
elim (s_produit_1 x1 x2 a l H11).
intros.
elim H23.
intros.
elim H25.
intros.
rewrite (s_produit_0 x1 x2 a x3 x4 H26 H27) in H11.
inversion H11.
cut (pl_compatible x3 x4).
intros.
elim H28.
intros.
elim H30.
intros.
rewrite <- H29 in H12.
elim (pl_produit_rec_3 d0 d1 tl x3 x4 x5 H12 H0 H31 H32 H).
intros.
split.
apply (rec_dta d0 a0 (app a tl) x1 H19).
exact (rec_st d0 x1 a tl x3 H26 H33).
apply (rec_dta d1 a1 (app a tl) x2 H20).
exact (rec_st d1 x2 a tl x4 H27 H34).
cut (st_compatible x1 x2).
intro.
exact (H28 a x3 x4 H26 H27).
apply (H0 x1 x2).
split with a0.
exact H19.
split with a1.
Admitted.

Lemma predta_inter_direct : forall (d0 d1 : preDTA) (a0 a1 : ad) (t : term), predta_compatible d0 d1 -> reconnaissance d0 a0 t -> reconnaissance d1 a1 t -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t.
Proof.
intro.
intro.
intro.
intro.
intro.
Admitted.

Lemma predta_inter_reciproque : forall (d0 d1 : preDTA) (a0 a1 : ad) (t : term), predta_compatible d0 d1 -> reconnaissance (preDTA_produit d0 d1) (iad_conv a0 a1) t -> reconnaissance d0 a0 t /\ reconnaissance d1 a1 t.
Proof.
intro.
intro.
intro.
intro.
intro.
Admitted.

Lemma inter_semantics : forall (d0 d1 : DTA) (sigma : signature) (t : term), dta_correct_wrt_sign d0 sigma -> dta_correct_wrt_sign d1 sigma -> (reconnait d0 t /\ reconnait d1 t <-> reconnait (inter d0 d1) t).
Proof.
Admitted.

Lemma inter_semantics_0 : forall (d0 d1 : DTA) (t : term), dta_compatible d0 d1 -> (reconnait d0 t /\ reconnait d1 t <-> reconnait (inter d0 d1) t).
Proof.
simple induction d0.
simple induction d1.
intros.
simpl in H.
simpl in |- *.
split.
intros.
elim H0.
intros.
exact (predta_inter_direct p p0 a a0 t H H1 H2).
intros.
exact (predta_inter_reciproque p p0 a a0 t H H0).
