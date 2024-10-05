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

Lemma pl_produit_path_incl_4 : forall (pl0 pl1 : prec_list) (n : nat) (plp : pl_path), pl_path_incl plp (pl_produit pl0 pl1) -> pl_tl_length pl0 n -> pl_tl_length pl1 n -> exists plp0 : pl_path, (exists plp1 : pl_path, plp = pl_path_product plp0 plp1 /\ pl_path_incl plp0 pl0 /\ pl_path_incl plp1 pl1).
Proof.
intros.
unfold pl_produit in H.
Admitted.

Lemma sproductl_0_0 : sproductl_0_def (M0 prec_list).
Proof.
unfold sproductl_0_def in |- *.
intros.
Admitted.

Lemma sproductl_0_1 : forall (a : ad) (a0 : prec_list), sproductl_0_def (M1 prec_list a a0).
Proof.
unfold sproductl_0_def in |- *.
intros.
simpl in H.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a1 c)); intro; rewrite H1 in H.
elim (bool_is_true_or_false (N.eqb a c)); intro; rewrite H2 in H0.
inversion H.
inversion H0.
rewrite (Neqb_complete _ _ H1).
rewrite (Neqb_complete _ _ H2).
simpl in |- *.
rewrite (Neqb_correct c).
simpl in |- *.
rewrite (Neqb_correct c).
trivial.
inversion H0.
Admitted.

Lemma sproductl_0_2 : forall m : state, sproductl_0_def m -> forall m0 : state, sproductl_0_def m0 -> sproductl_0_def (M2 prec_list m m0).
Proof.
unfold sproductl_0_def in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a c)); intro.
rewrite H3 in H1.
inversion H1.
rewrite (Neqb_complete _ _ H3).
induction c as [| p0].
simpl in |- *.
elim (H N0 r0 N0 r0 r1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
elim (H0 (Npos p0) r0 (Npos p0) r0 r1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H (Npos p0) r0 (Npos p0) r0 r1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 N0 r0 N0 r0 r1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
rewrite H3 in H1.
Admitted.

Lemma sproductl_0_3 : forall m : state, sproductl_0_def m.
Proof.
Admitted.

Lemma sproductl_0 : forall (s : state) (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list), MapGet prec_list (M1 prec_list a p) c = Some r0 -> MapGet prec_list s c = Some r1 -> MapGet prec_list (s_produit_l a p s) c = Some (pl_produit r0 r1).
Proof.
Admitted.

Lemma sproductl_1_0 : sproductl_1_def (M0 prec_list).
Proof.
unfold sproductl_1_def in |- *.
intros.
Admitted.

Lemma sproductl_1_1 : forall (a : ad) (a0 : prec_list), sproductl_1_def (M1 prec_list a a0).
Proof.
unfold sproductl_1_def in |- *.
intros.
simpl in H.
elim (bool_is_true_or_false (N.eqb a1 a)); intro; rewrite H0 in H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a1 c)); intro; rewrite H1 in H.
split with p.
split with a0.
simpl in |- *.
split.
rewrite H1.
reflexivity.
rewrite <- (Neqb_complete _ _ H0).
rewrite H1.
reflexivity.
inversion H.
Admitted.

Lemma sproductl_1_2 : forall m : state, sproductl_1_def m -> forall m0 : state, sproductl_1_def m0 -> sproductl_1_def (M2 prec_list m m0).
Proof.
unfold sproductl_1_def in |- *.
intros.
induction a as [| p0].
induction c as [| p0].
simpl in H1.
elim (H N0 p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x.
split with x0.
split.
exact H4.
simpl in |- *.
exact H5.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
inversion H1.
simpl in H1.
elim (H N0 p (Npos p0) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x.
split with x0.
split.
exact H4.
simpl in |- *.
exact H5.
simpl in H1.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
induction c as [| p1].
simpl in H1.
inversion H1.
simpl in H1.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
elim (H0 (Npos p0) p (Npos p1) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
intros.
split with x.
split with x0.
split.
exact H4.
simpl in |- *.
exact H5.
inversion H1.
elim (H0 (Npos p0) p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
induction c as [| p1].
simpl in H1.
elim (H (Npos p0) p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
simpl in H1.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
inversion H1.
elim (H (Npos p0) p (Npos p1) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
inversion H1.
induction c as [| p0].
simpl in H1.
inversion H1.
simpl in H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
elim (H0 N0 p (Npos p0) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x.
split with x0.
simpl in |- *.
simpl in H4.
split.
exact H4.
exact H5.
inversion H1.
elim (H0 N0 p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
Admitted.

Lemma sproductl_1_3 : forall m : state, sproductl_1_def m.
Proof.
Admitted.

Lemma sproductl_1 : forall (s : state) (a : ad) (p : prec_list) (c : ad) (r : prec_list), MapGet prec_list (s_produit_l a p s) c = Some r -> exists r0 : prec_list, (exists r1 : prec_list, MapGet prec_list (M1 prec_list a p) c = Some r0 /\ MapGet prec_list s c = Some r1).
Proof.
Admitted.

Lemma sproductr_0_0 : sproductr_0_def (M0 prec_list).
Proof.
unfold sproductr_0_def in |- *.
intros.
Admitted.

Lemma sproductr_0_1 : forall (a : ad) (a0 : prec_list), sproductr_0_def (M1 prec_list a a0).
Proof.
unfold sproductr_0_def in |- *.
intros.
simpl in H.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a1 c)); intro; rewrite H1 in H.
elim (bool_is_true_or_false (N.eqb a c)); intro; rewrite H2 in H0.
inversion H.
inversion H0.
rewrite (Neqb_complete _ _ H1).
rewrite (Neqb_complete _ _ H2).
simpl in |- *.
rewrite (Neqb_correct c).
simpl in |- *.
rewrite (Neqb_correct c).
trivial.
inversion H0.
Admitted.

Lemma sproductr_0_2 : forall m : state, sproductr_0_def m -> forall m0 : state, sproductr_0_def m0 -> sproductr_0_def (M2 prec_list m m0).
Proof.
unfold sproductr_0_def in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a c)); intro; rewrite H3 in H1.
inversion H1.
rewrite (Neqb_complete _ _ H3).
induction c as [| p0].
simpl in |- *.
elim (H N0 r0 N0 r0 r1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
elim (H0 (Npos p0) r0 (Npos p0) r0 r1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H (Npos p0) r0 (Npos p0) r0 r1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 N0 r0 N0 r0 r1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
Admitted.

Lemma sproductr_0_3 : forall m : state, sproductr_0_def m.
Proof.
Admitted.

Lemma sproductr_0 : forall (s : state) (a : ad) (p : prec_list) (c : ad) (r0 r1 : prec_list), MapGet prec_list (M1 prec_list a p) c = Some r0 -> MapGet prec_list s c = Some r1 -> MapGet prec_list (s_produit_r a p s) c = Some (pl_produit r1 r0).
Proof.
Admitted.

Lemma sproductr_1_0 : sproductr_1_def (M0 prec_list).
Proof.
unfold sproductr_1_def in |- *.
intros.
Admitted.

Lemma sproductr_1_1 : forall (a : ad) (a0 : prec_list), sproductr_1_def (M1 prec_list a a0).
Proof.
unfold sproductr_1_def in |- *.
intros.
simpl in H.
elim (bool_is_true_or_false (N.eqb a1 a)); intro; rewrite H0 in H.
simpl in H.
elim (bool_is_true_or_false (N.eqb a1 c)); intro; rewrite H1 in H.
split with p.
split with a0.
simpl in |- *.
split.
rewrite H1.
reflexivity.
rewrite <- (Neqb_complete _ _ H0).
rewrite H1.
reflexivity.
inversion H.
Admitted.

Lemma sproductr_1_2 : forall m : state, sproductr_1_def m -> forall m0 : state, sproductr_1_def m0 -> sproductr_1_def (M2 prec_list m m0).
Proof.
unfold sproductr_1_def in |- *.
intros.
induction a as [| p0].
induction c as [| p0].
simpl in H1.
elim (H N0 p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
simpl in H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
inversion H1.
simpl in H1.
elim (H N0 p (Npos p0) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
induction c as [| p1].
simpl in H1.
inversion H1.
simpl in H1.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
elim (H0 (Npos p0) p (Npos p1) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
inversion H1.
elim (H0 (Npos p0) p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
induction c as [| p1].
simpl in H1.
elim (H (Npos p0) p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
simpl in H1.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
inversion H1.
elim (H (Npos p0) p (Npos p1) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
inversion H1.
induction c as [| p0].
simpl in H1.
inversion H1.
simpl in H.
simpl in H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
elim (H0 N0 p (Npos p0) r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
exact H5.
inversion H1.
elim (H0 N0 p N0 r H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H4.
intros.
split with x.
split with x0.
simpl in |- *.
split.
simpl in H4.
exact H4.
Admitted.

Lemma sproductr_1_3 : forall m : state, sproductr_1_def m.
Proof.
Admitted.

Lemma s_produit_0 : forall (s0 s1 : state) (c : ad) (p0 p1 : prec_list), MapGet prec_list s0 c = Some p0 -> MapGet prec_list s1 c = Some p1 -> MapGet prec_list (s_produit s0 s1) c = Some (pl_produit p0 p1).
Proof.
simple induction s0.
intros.
inversion H.
intros.
induction s1 as [| a1 a2| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
inversion H0.
unfold s_produit in |- *.
exact (sproductl_0 (M1 prec_list a1 a2) a a0 c p0 p1 H H0).
unfold s_produit in |- *.
exact (sproductl_0 (M2 prec_list s1_1 s1_0) a a0 c p0 p1 H H0).
intros.
induction s1 as [| a a0| s1_1 Hrecs1_1 s1_0 Hrecs1_0].
inversion H2.
unfold s_produit in |- *.
exact (sproductr_0 (M2 prec_list m m0) a a0 c p1 p0 H2 H1).
induction c as [| p].
simpl in |- *.
simpl in H1.
simpl in H2.
exact (H s1_1 N0 p0 p1 H1 H2).
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
simpl in H1.
simpl in H2.
exact (H0 s1_0 (Npos p) p0 p1 H1 H2).
simpl in H1.
simpl in H2.
simpl in |- *.
exact (H s1_1 (Npos p) p0 p1 H1 H2).
simpl in |- *.
simpl in H1.
simpl in H2.
Admitted.

Lemma s_produit_1 : forall (s0 s1 : state) (c : ad) (p : prec_list), MapGet prec_list (s_produit s0 s1) c = Some p -> exists p0 : prec_list, (exists p1 : prec_list, MapGet prec_list s0 c = Some p0 /\ MapGet prec_list s1 c = Some p1).
Proof.
simple induction s0.
simple induction s1.
intros.
simpl in H.
inversion H.
intros.
simpl in H.
inversion H.
intros.
simpl in H1.
inversion H1.
simple induction s1.
intros.
simpl in H.
inversion H.
intros.
unfold s_produit in H.
exact (sproductl_1 (M1 prec_list a1 a2) a a0 c p H).
intros.
simpl in H.
unfold s_produit in H1.
exact (sproductl_1 (M2 prec_list m m0) a a0 c p H1).
simple induction s1; intros.
inversion H1.
unfold s_produit in H1.
elim (sproductr_1 (M2 prec_list m m0) a a0 c p H1).
intros.
elim H2.
intros.
elim H3.
intros.
split with x0.
split with x.
split.
exact H5.
exact H4.
induction c as [| p0].
simpl in H3.
elim (H m1 N0 p H3).
intros.
elim H4.
intros.
elim H5.
intros.
split with x.
split with x0.
split.
simpl in |- *.
exact H6.
simpl in |- *.
exact H7.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H3.
elim (H0 m2 (Npos p0) p H3).
intros.
elim H4.
intros.
elim H5.
intros.
split with x.
split with x0.
simpl in |- *.
split.
exact H6.
exact H7.
simpl in H3.
elim (H m1 (Npos p0) p H3).
intros.
elim H4.
intros.
elim H5.
intros.
split with x.
split with x0.
simpl in |- *.
split.
exact H6.
exact H7.
simpl in H3.
elim (H0 m2 N0 p H3).
intros.
elim H4.
intros.
elim H5.
intros.
split with x.
split with x0.
simpl in |- *.
split.
exact H6.
Admitted.

Lemma predta_produit_0_0 : predta_produit_0d_def (M0 state).
Proof.
unfold predta_produit_0d_def in |- *.
intros.
Admitted.

Lemma predta_produit_0_1 : forall (a : ad) (a0 : state), predta_produit_0d_def (M1 state a a0).
Proof.
unfold predta_produit_0d_def in |- *.
intros.
simpl in H.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a1 a2)); intro; rewrite H1 in H.
rewrite (Neqb_complete a1 a2 H1).
elim (bool_is_true_or_false (N.eqb a a3)); intro; rewrite H2 in H0.
rewrite (Neqb_complete a a3 H2).
inversion H.
inversion H0.
simpl in |- *.
rewrite (Neqb_correct (iad_conv a2 a3)).
trivial.
inversion H0.
Admitted.

Lemma predta_produit_0_2 : forall m : preDTA, predta_produit_0d_def m -> forall m0 : preDTA, predta_produit_0d_def m0 -> predta_produit_0d_def (M2 state m m0).
Proof.
unfold predta_produit_0d_def in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a a0)); intro; rewrite H3 in H1.
inversion H1.
induction a1 as [| p].
induction a0 as [| p].
rewrite (Neqb_complete a N0 H3).
simpl in |- *.
elim (H N0 s0 N0 N0 s0 s1).
simpl in |- *.
trivial.
simpl in |- *.
trivial.
simpl in H2.
exact H2.
induction p as [p Hrecp| p Hrecp| ].
rewrite (Neqb_complete _ _ H3).
simpl in |- *.
elim (H (Npos p) s0 (Npos p) N0 s0 s1).
simpl in |- *.
trivial.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
trivial.
simpl in H2.
assumption.
rewrite (Neqb_complete _ _ H3).
simpl in |- *.
elim (H (Npos p) s0 (Npos p) N0 s0 s1).
simpl in |- *.
trivial.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
trivial.
simpl in H2.
trivial.
rewrite (Neqb_complete _ _ H3).
simpl in |- *.
elim (H N0 s0 N0 N0 s0 s1).
simpl in |- *.
trivial.
simpl in |- *.
trivial.
simpl in H2.
trivial.
induction p as [p Hrecp| p Hrecp| ].
rewrite (Neqb_complete _ _ H3).
induction a0 as [| p0].
simpl in |- *.
elim (H0 N0 s0 N0 (Npos p) s0 s1).
simpl in |- *.
trivial.
reflexivity.
simpl in H2.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
simpl in H2.
elim (H0 (Npos p0) s0 (Npos p0) (Npos p) s0 s1).
simpl in |- *.
trivial.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
trivial.
exact H2.
simpl in |- *.
elim (H0 (Npos p0) s0 (Npos p0) (Npos p) s0 s1).
simpl in |- *.
trivial.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
trivial.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 N0 s0 N0 (Npos p) s0 s1).
simpl in |- *.
reflexivity.
reflexivity.
simpl in H2.
exact H2.
rewrite (Neqb_complete _ _ H3).
induction a0 as [| p0].
simpl in |- *.
elim (H N0 s0 N0 (Npos p) s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
elim (H (Npos p0) s0 (Npos p0) (Npos p) s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H (Npos p0) s0 (Npos p0) (Npos p) s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p0).
trivial.
simpl in H2.
exact H2.
simpl in |- *.
elim (H N0 s0 N0 (Npos p) s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
rewrite (Neqb_complete _ _ H3).
induction a0 as [| p].
simpl in |- *.
elim (H0 N0 s0 N0 N0 s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
elim (H0 (Npos p) s0 (Npos p) N0 s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
trivial.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 (Npos p) s0 (Npos p) N0 s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 N0 s0 N0 N0 s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
Admitted.

Lemma predta_produit_0_3 : forall m : preDTA, predta_produit_0d_def m.
Proof.
Admitted.

Lemma predta_produit_0 : forall (a : ad) (s : state) (d : preDTA) (a0 a1 : ad) (s0 s1 : state), MapGet state (M1 state a s) a0 = Some s0 -> MapGet state d a1 = Some s1 -> MapGet state (preDTA_produit_l a s d) (iad_conv a0 a1) = Some (s_produit s0 s1).
Proof.
intros.
Admitted.

Lemma predta_produit_1_0 : predta_produit_1_def (M0 state).
Proof.
unfold predta_produit_1_def in |- *.
intros.
Admitted.

Lemma predta_produit_1_1 : forall (a : ad) (a0 : state), predta_produit_1_def (M1 state a a0).
Proof.
unfold predta_produit_1_def in |- *.
intros.
simpl in H.
simpl in H0.
elim (bool_is_true_or_false (N.eqb a1 a2)); intro; rewrite H1 in H.
elim (bool_is_true_or_false (N.eqb a a3)); intro; rewrite H2 in H0.
inversion H.
inversion H0.
rewrite (Neqb_complete _ _ H1).
rewrite (Neqb_complete _ _ H2).
simpl in |- *.
rewrite (Neqb_correct (iad_conv a3 a2)).
trivial.
inversion H0.
Admitted.

Lemma predta_produit_1_2 : forall m : preDTA, predta_produit_1_def m -> forall m0 : preDTA, predta_produit_1_def m0 -> predta_produit_1_def (M2 state m m0).
Proof.
unfold predta_produit_1_def in |- *.
intros.
simpl in H1.
elim (bool_is_true_or_false (N.eqb a a0)); intro; rewrite H3 in H1.
rewrite (Neqb_complete _ _ H3).
inversion H1.
induction a0 as [| p].
induction a1 as [| p].
simpl in |- *.
elim (H N0 s0 N0 N0 s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
elim (H0 N0 s0 N0 (Npos p) s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H N0 s0 N0 (Npos p) s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 N0 s0 N0 N0 s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
induction p as [p Hrecp| p Hrecp| ].
induction a1 as [| p0].
simpl in |- *.
elim (H (Npos p) s0 (Npos p) N0 s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
elim (H0 (Npos p) s0 (Npos p) (Npos p0) s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H (Npos p) s0 (Npos p) (Npos p0) s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 (Npos p) s0 (Npos p) N0 s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
induction a1 as [| p0].
simpl in |- *.
elim (H (Npos p) s0 (Npos p) N0 s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
elim (H0 (Npos p) s0 (Npos p) (Npos p0) s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H (Npos p) s0 (Npos p) (Npos p0) s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 (Npos p) s0 (Npos p) N0 s0 s1).
reflexivity.
simpl in |- *.
rewrite (aux_Neqb_1_0 p).
reflexivity.
simpl in H2.
exact H2.
induction a1 as [| p].
simpl in |- *.
elim (H N0 s0 N0 N0 s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
elim (H0 N0 s0 N0 (Npos p) s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H N0 s0 N0 (Npos p) s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
simpl in |- *.
elim (H0 N0 s0 N0 N0 s0 s1).
reflexivity.
reflexivity.
simpl in H2.
exact H2.
Admitted.

Lemma predta_produit_1_3 : forall m : preDTA, predta_produit_1_def m.
Proof.
Admitted.

Lemma predta_produit_1 : forall (a : ad) (s : state) (d : preDTA) (a0 a1 : ad) (s0 s1 : state), MapGet state (M1 state a s) a0 = Some s0 -> MapGet state d a1 = Some s1 -> MapGet state (preDTA_produit_r a s d) (iad_conv a1 a0) = Some (s_produit s1 s0).
Proof.
intros.
Admitted.

Lemma predta_produit_2 : forall (d0 d1 : preDTA) (a0 a1 : ad) (s0 s1 : state), MapGet state d0 a0 = Some s0 -> MapGet state d1 a1 = Some s1 -> MapGet state (preDTA_produit d0 d1) (iad_conv a0 a1) = Some (s_produit s0 s1).
Proof.
simple induction d0.
intros.
inversion H.
intros.
induction d1 as [| a3 a4| d1_1 Hrecd1_1 d1_0 Hrecd1_0]; unfold preDTA_produit in |- *.
inversion H0.
exact (predta_produit_0 a a0 (M1 state a3 a4) a1 a2 s0 s1 H H0).
exact (predta_produit_0 a a0 (M2 state d1_1 d1_0) a1 a2 s0 s1 H H0).
intros.
induction d1 as [| a a2| d1_1 Hrecd1_1 d1_0 Hrecd1_0].
inversion H2.
unfold preDTA_produit in |- *.
exact (predta_produit_1 a a2 (M2 state m m0) a1 a0 s1 s0 H2 H1).
induction a0 as [| p].
induction a1 as [| p].
simpl in |- *.
simpl in H1.
simpl in H2.
exact (H d1_1 N0 N0 s0 s1 H1 H2).
induction p as [p Hrecp| p Hrecp| ].
simpl in |- *.
simpl in H1.
simpl in H2.
exact (H d1_0 N0 (Npos p) s0 s1 H1 H2).
simpl in |- *.
simpl in H1.
simpl in H2.
exact (H d1_1 N0 (Npos p) s0 s1 H1 H2).
simpl in |- *.
exact (H d1_0 N0 N0 s0 s1 H1 H2).
simpl in H1.
induction p as [p Hrecp| p Hrecp| ].
induction a1 as [| p0].
simpl in H2.
simpl in |- *.
exact (H0 d1_1 (Npos p) N0 s0 s1 H1 H2).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
simpl in H2.
exact (H0 d1_0 (Npos p) (Npos p0) s0 s1 H1 H2).
simpl in |- *.
exact (H0 d1_1 (Npos p) (Npos p0) s0 s1 H1 H2).
simpl in H2.
simpl in |- *.
exact (H0 d1_0 (Npos p) N0 s0 s1 H1 H2).
induction a1 as [| p0].
simpl in H2.
simpl in |- *.
exact (H d1_1 (Npos p) N0 s0 s1 H1 H2).
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in |- *.
simpl in H2.
simpl in H1.
exact (H d1_0 (Npos p) (Npos p0) s0 s1 H1 H2).
simpl in |- *.
simpl in H2.
exact (H d1_1 (Npos p) (Npos p0) s0 s1 H1 H2).
simpl in H2.
simpl in |- *.
exact (H d1_0 (Npos p) N0 s0 s1 H1 H2).
induction a1 as [| p].
simpl in H2.
simpl in |- *.
exact (H0 d1_1 N0 N0 s0 s1 H1 H2).
induction p as [p Hrecp| p Hrecp| ].
simpl in H2.
simpl in |- *.
exact (H0 d1_0 N0 (Npos p) s0 s1 H1 H2).
simpl in H2.
simpl in |- *.
exact (H0 d1_1 N0 (Npos p) s0 s1 H1 H2).
simpl in H2.
simpl in |- *.
Admitted.

Lemma predta_produit_3_0 : predta_produit_3_def (M0 state).
Proof.
unfold predta_produit_3_def in |- *.
intros.
simpl in H.
Admitted.

Lemma predta_produit_3_1 : forall (a : ad) (a0 : state), predta_produit_3_def (M1 state a a0).
Proof.
unfold predta_produit_3_def in |- *.
intros.
simpl in H.
split with a2.
split with a.
split with s0.
split with a0.
elim (bool_is_true_or_false (N.eqb (iad_conv a2 a) a1)); intro.
rewrite (Neqb_complete _ _ H0).
split.
reflexivity.
split.
simpl in |- *.
rewrite (Neqb_correct a2).
reflexivity.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
rewrite H0 in H.
Admitted.

Lemma predta_produit_3_2 : forall m : preDTA, predta_produit_3_def m -> forall m0 : preDTA, predta_produit_3_def m0 -> predta_produit_3_def (M2 state m m0).
Proof.
unfold predta_produit_3_def in |- *.
intros.
elim (iad_conv_surj a).
intros.
elim H2.
intros.
rewrite H3 in H1.
rewrite H3.
induction a0 as [| p].
induction x as [| p].
induction x0 as [| p].
simpl in H1.
elim (H N0 N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with N0.
split with x1.
split with x2.
split.
reflexivity.
elim (iad_conv_inj N0 N0 x x0 H8).
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p as [p Hrecp| p Hrecp| ].
simpl in H1.
elim (H0 (Npos (iad_conv_aux_0 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with (Npos (xI p)).
split with x1.
split with x2.
split.
reflexivity.
elim (iad_conv_inj N0 (Npos p) x x0 H8).
intros.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H (Npos (iad_conv_aux_0 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with (Npos (xO p)).
split with x1.
split with x2.
elim (iad_conv_inj N0 (Npos p) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H0 N0 N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p as [p Hrecp| p Hrecp| ].
induction x0 as [| p0].
simpl in H1.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction x0 as [| p0].
simpl in H1.
elim (H (Npos (iad_conv_aux_1 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p)).
split with N0.
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
clear Hrecp0.
clear Hrecp.
simpl in H1.
elim (H0 (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p)).
split with (Npos (xI p0)).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
clear Hrecp0.
simpl in H1.
elim (H (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p)).
split with (Npos (xO p0)).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H0 (Npos (iad_conv_aux_1 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p)).
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction x0 as [| p].
simpl in H1.
inversion H1.
induction p as [p Hrecp| p Hrecp| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction p as [p Hrecp| p Hrecp| ].
induction x as [| p0].
induction x0 as [| p0].
simpl in H1.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
induction x0 as [| p1].
simpl in H1.
elim (H (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p0)).
split with N0.
split with x1.
split with x2.
elim (iad_conv_inj (Npos p0) N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
clear Hrecp1.
clear Hrecp0.
simpl in H1.
elim (H0 (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p0)).
split with (Npos (xI p1)).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
clear Hrecp1.
clear Hrecp0.
simpl in H1.
elim (H (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p0)).
split with (Npos (xO p1)).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
clear Hrecp0.
simpl in H1.
elim (H0 (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p0)).
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p0) N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction x0 as [| p1].
simpl in H1.
inversion H1.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction x0 as [| p0].
simpl in H1.
elim (H N0 (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with N0.
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
elim (H0 (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with (Npos (xI p0)).
split with x1.
split with x2.
elim (iad_conv_inj N0 (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with (Npos (xO p0)).
split with x1.
split with x2.
elim (iad_conv_inj N0 (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H0 N0 (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction x as [| p0].
induction x0 as [| p0].
simpl in H1.
elim (H N0 (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with N0.
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 x x0).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in |- *.
exact H8.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
elim (H0 (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with (Npos (xI p0)).
split with x1.
split with x2.
elim (iad_conv_inj N0 (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H (Npos (iad_conv_aux_0 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with (Npos (xO p0)).
split with x1.
split with x2.
elim (iad_conv_inj N0 (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H0 N0 (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with N0.
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
induction x0 as [| p1].
simpl in H1.
inversion H1.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction x0 as [| p1].
simpl in H1.
elim (H (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p0)).
split with N0.
split with x1.
split with x2.
elim (iad_conv_inj (Npos p0) N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p1 as [p1 Hrecp1| p1 Hrecp1| ].
clear Hrecp1.
clear Hrecp0.
simpl in H1.
elim (H0 (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p0)).
split with (Npos (xI p1)).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
clear Hrecp1.
clear Hrecp0.
simpl in H1.
elim (H (Npos (iad_conv_aux_2 p0 p1)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p0)).
split with (Npos (xO p1)).
split with x1.
elim (iad_conv_inj (Npos p0) (Npos p1) x x0 H8).
intros.
intros.
rewrite <- H12 in H10.
split with x2.
split.
reflexivity.
rewrite <- H13 in H11.
split.
simpl in |- *.
simpl in H10.
exact H10.
exact H11.
simpl in H1.
elim (H0 (Npos (iad_conv_aux_1 p0)) (Npos p) s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xO p0)).
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p0) N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction x0 as [| p0].
simpl in H1.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction x as [| p].
induction x0 as [| p].
simpl in H1.
inversion H1.
induction p as [p Hrecp| p Hrecp| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction p as [p Hrecp| p Hrecp| ].
induction x0 as [| p0].
simpl in H1.
elim (H (Npos (iad_conv_aux_1 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p)).
split with N0.
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
elim (H0 (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p)).
split with (Npos (xI p0)).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H (Npos (iad_conv_aux_2 p p0)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p)).
split with (Npos (xO p0)).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) (Npos p0) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H0 (Npos (iad_conv_aux_1 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos (xI p)).
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj (Npos p) N0 x x0 H8).
intros.
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction x0 as [| p0].
simpl in H1.
inversion H1.
induction p0 as [p0 Hrecp0| p0 Hrecp0| ].
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
simpl in H1.
inversion H1.
induction x0 as [| p].
simpl in H1.
elim (H N0 N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with N0.
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
induction p as [p Hrecp| p Hrecp| ].
simpl in H1.
elim (H0 (Npos (iad_conv_aux_0 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with (Npos (xI p)).
split with x1.
split with x2.
elim (iad_conv_inj N0 (Npos p) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H (Npos (iad_conv_aux_0 p)) N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with (Npos (xO p)).
split with x1.
split with x2.
elim (iad_conv_inj N0 (Npos p) x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
exact H11.
simpl in H1.
elim (H0 N0 N0 s s0 H1).
intros.
elim H4.
intros.
elim H5.
intros.
elim H6.
intros.
elim H7.
intros.
elim H9.
intros.
split with (Npos 1).
split with (Npos 1).
split with x1.
split with x2.
elim (iad_conv_inj N0 N0 x x0 H8).
intros.
split.
reflexivity.
intros.
rewrite <- H12 in H10.
rewrite <- H13 in H11.
split.
exact H10.
Admitted.

Lemma predta_produit_3_3 : forall m : preDTA, predta_produit_3_def m.
Proof.
Admitted.

Lemma predta_produit_3 : forall (d0 : preDTA) (a a0 : ad) (s s0 : state), MapGet state (preDTA_produit_l a0 s0 d0) a = Some s -> exists a1 : ad, (exists a2 : ad, (exists s1 : state, (exists s2 : state, a = iad_conv a1 a2 /\ MapGet state (M1 state a0 s0) a1 = Some s1 /\ MapGet state d0 a2 = Some s2))).
Proof.
Admitted.

Lemma predta_produit_4_0 : predta_produit_4_def (M0 state).
Proof.
unfold predta_produit_4_def in |- *.
intros.
Admitted.

Lemma predta_produit_4_1 : forall (a : ad) (a0 : state), predta_produit_4_def (M1 state a a0).
Proof.
unfold predta_produit_4_def in |- *.
intros.
simpl in H.
elim (bool_is_true_or_false (N.eqb (iad_conv a a2) a1)).
intro.
rewrite H0 in H.
inversion H.
split with a.
split with a2.
split with s0.
split with a0.
split.
symmetry in |- *.
exact (Neqb_complete _ _ H0).
split.
simpl in |- *.
rewrite (Neqb_correct a2).
reflexivity.
simpl in |- *.
rewrite (Neqb_correct a).
reflexivity.
intro.
rewrite H0 in H.
Admitted.

Lemma sproductr_1 : forall (s : state) (a : ad) (p : prec_list) (c : ad) (r : prec_list), MapGet prec_list (s_produit_r a p s) c = Some r -> exists r0 : prec_list, (exists r1 : prec_list, MapGet prec_list (M1 prec_list a p) c = Some r0 /\ MapGet prec_list s c = Some r1).
Proof.
exact (Map_ind prec_list sproductr_1_def sproductr_1_0 sproductr_1_1 sproductr_1_2).
