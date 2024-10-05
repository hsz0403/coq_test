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

Lemma pl_product_0_4 : forall (a : ad) (la ls p : prec_list), pl_produit_0_incr la p -> pl_produit_1_incr ls p -> pl_produit_1_incr (prec_cons a la ls) p.
Proof.
unfold pl_produit_0_incr in |- *.
unfold pl_produit_1_incr in |- *.
intros.
induction n as [| n Hrecn].
elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 (prec_cons a la ls) p) H1)).
elim (nat_sum (pl_essence (prec_cons a la ls) p)); intro.
elim (le_Sn_O 0).
exact (eq_ind (pl_essence (prec_cons a la ls) p) (fun n : nat => 1 <= n) (pl_ess_invar_0 (prec_cons a la ls) p) 0 H2).
elim H2.
intros.
rewrite H3.
induction p as [a0 p1 Hrecp1 p0 Hrecp0| ].
replace (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons a0 p1 p0)) with (pl_produit_0 a la (prec_cons a0 p1 p0) x (pl_produit_1 ls x (prec_cons a0 p1 p0))).
replace (pl_produit_1 (prec_cons a la ls) (S n) (prec_cons a0 p1 p0)) with (pl_produit_0 a la (prec_cons a0 p1 p0) n (pl_produit_1 ls n (prec_cons a0 p1 p0))).
rewrite <- (H0 x).
rewrite <- (H0 n).
rewrite <- (H a (pl_produit_1 ls (pl_essence ls (prec_cons a0 p1 p0)) (prec_cons a0 p1 p0)) x).
rewrite <- (H a (pl_produit_1 ls (pl_essence ls (prec_cons a0 p1 p0)) (prec_cons a0 p1 p0)) n).
reflexivity.
exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_1 a a0 la ls p1 p0) H1)).
exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_1 a a0 la ls p1 p0) (eq_ind (pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0)) (fun z : nat => pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0) <= z) (le_n_n (pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0))) (S x) H3))).
exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_2 a a0 la ls p1 p0) H1)).
exact (le_S_n _ _ (le_trans _ _ _ (pl_ess_invar_2 a a0 la ls p1 p0) (eq_ind (pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0)) (fun z : nat => pl_essence (prec_cons a la ls) (prec_cons a0 p1 p0) <= z) (le_n_n _) (S x) H3))).
reflexivity.
reflexivity.
simpl in |- *.
Admitted.

Lemma pl_product_0_5 : forall p p' : prec_list, pl_produit_0_incr p p' /\ pl_produit_1_incr p p'.
Proof.
Admitted.

Lemma pl_product_0 : forall p0 p1 : prec_list, (forall (a : ad) (l : prec_list) (n : nat), pl_essence p0 p1 <= n -> pl_produit_0 a p0 p1 (pl_essence p0 p1) l = pl_produit_0 a p0 p1 n l) /\ (forall n : nat, pl_essence p0 p1 <= n -> pl_produit_1 p0 (pl_essence p0 p1) p1 = pl_produit_1 p0 n p1).
Proof.
Admitted.

Lemma pl_product_0_invar_essence : forall (p0 p1 : prec_list) (n : nat), pl_essence p0 p1 <= n -> pl_produit_1 p0 (pl_essence p0 p1) p1 = pl_produit_1 p0 n p1.
Proof.
intro.
intro.
elim (pl_product_0 p0 p1).
intros.
Admitted.

Lemma pl_product_1 : forall (a : ad) (la pl l : prec_list) (n : nat), pl_essence la pl <= n -> pl_produit_0 a la pl n l = prec_empty -> pl = prec_empty.
Proof.
intros.
induction n as [| n Hrecn].
elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 la pl) H)).
induction pl as [a0 pl1 Hrecpl1 pl0 Hrecpl0| ].
simpl in H0.
inversion H0.
Admitted.

Lemma pl_tl_length_prod_0 : forall p : prec_list, pl_tl_length_prod_def_0 p prec_empty.
Proof.
unfold pl_tl_length_prod_def_0 in |- *.
intros.
split.
intros.
inversion H2.
intros.
split.
intros.
elim (nat_sum m); intro.
rewrite H4 in H.
elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 p prec_empty) H)).
elim H4.
intros.
rewrite H5.
simpl in |- *.
exact H3.
intros.
elim (nat_sum m).
intro.
rewrite H4.
reflexivity.
intros.
elim H4.
elim H4.
intros.
rewrite H5.
simpl in |- *.
Admitted.

Lemma pl_tl_length_prod_1 : forall p : prec_list, pl_tl_length_prod_def_1 p prec_empty.
Proof.
unfold pl_tl_length_prod_def_1 in |- *.
intros.
elim (nat_sum m); intros.
rewrite H2.
simpl in |- *.
exact H0.
elim H2.
intros.
rewrite H3.
simpl in |- *.
Admitted.

Lemma pl_tl_length_prod_2 : forall p : prec_list, pl_tl_length_prod_def_1 prec_empty p.
Proof.
unfold pl_tl_length_prod_def_1 in |- *.
intros.
elim (nat_sum m); intros.
rewrite H2.
simpl in |- *.
exact H.
elim H2.
intros.
rewrite H3.
simpl in |- *.
Admitted.

Lemma pl_tl_length_prod_3 : forall (a : ad) (la ls p : prec_list), pl_tl_length_prod_def_0 p ls -> pl_tl_length_prod_def_1 p la -> pl_tl_length_prod_def_0 p (prec_cons a la ls).
Proof.
unfold pl_tl_length_prod_def_0 in |- *.
unfold pl_tl_length_prod_def_1 in |- *.
intros.
split.
intros.
elim (nat_sum m); intro.
rewrite H5 in H1.
elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 p (prec_cons a la ls)) H1)).
elim H5.
intros.
rewrite H6.
replace (pl_produit_0 a0 p (prec_cons a la ls) (S x) l) with (prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)).
elim (H l a0 n x).
intros.
cut (pl_tl_length (pl_produit_1 p x la) n).
intro.
inversion H4.
elim H3.
intros.
elim (H8 (sym_eq H13)).
intros.
apply (pl_tl_propag (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p prec_empty x l) n H9).
elim (nat_sum x); intro.
rewrite H18 in H16.
simpl in H16.
cut (pl_tl_length prec_empty (S n)).
intro.
inversion H19.
exact (H16 H15).
elim H18.
intros.
rewrite H19.
simpl in |- *.
exact H15.
intro.
replace (pl_produit_0 a0 p prec_empty x l) with prec_empty.
exact (pl_tl_S (iad_conv a0 a) (pl_produit_1 p x la) n H9).
elim (nat_sum x); intro.
rewrite H16.
reflexivity.
elim H16.
intros.
rewrite H17.
simpl in |- *.
symmetry in |- *.
exact H15.
exact (pl_tl_propag (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l) n H9 (H7 H15)).
apply (H0 n x H2).
inversion H4.
exact H10.
exact H11.
unfold pl_essence in |- *.
unfold pl_essence in H1.
rewrite H6 in H1.
simpl in H1.
elim (le_or_lt (pl_card p + pl_card la) x); intro.
exact H9.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)).
rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)).
simpl in |- *.
apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))).
exact (le_trans _ _ _ (lt_le_S _ _ H9) (plus_le_compat (pl_card p) (pl_card p) (pl_card la) (pl_card la + pl_card ls) (le_n_n _) (le_plus_l _ _))).
exact H1.
unfold pl_essence in |- *.
unfold pl_essence in H1.
rewrite H6 in H1.
simpl in H1.
elim (le_or_lt (pl_card p + pl_card ls) x); intro.
exact H7.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)).
rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)).
simpl in |- *.
apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))).
exact (le_trans _ _ _ (lt_le_S _ _ H7) (plus_le_compat (pl_card p) (pl_card p) (pl_card ls) (pl_card la + pl_card ls) (le_n_n _) (le_plus_r _ _))).
exact H1.
exact H2.
exact H3.
reflexivity.
intros.
Admitted.

Lemma pl_tl_length_prod_4 : forall (a : ad) (la ls p : prec_list), pl_tl_length_prod_def_0 la p -> pl_tl_length_prod_def_1 ls p -> pl_tl_length_prod_def_1 (prec_cons a la ls) p.
Proof.
unfold pl_tl_length_prod_def_0 in |- *.
unfold pl_tl_length_prod_def_1 in |- *.
intros.
elim (nat_sum m); intros.
rewrite H4 in H3.
elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 (prec_cons a la ls) p) H3)).
elim H4.
intros.
rewrite H5.
elim (pl_sum p).
intros.
rewrite H6 in H2.
inversion H2.
rewrite <- H8 in H1.
inversion H1.
intros.
elim H6.
intros.
elim H7.
intros.
elim H8.
intros.
rewrite H9.
replace (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons x0 x1 x2)) with (pl_produit_0 a la (prec_cons x0 x1 x2) x (pl_produit_1 ls x (prec_cons x0 x1 x2))).
inversion H1.
rewrite <- H9.
elim (H (pl_produit_1 prec_empty x p) a n0 x).
intros.
rewrite <- H11 in H2.
exact (H15 H2).
rewrite H5 in H3.
unfold pl_essence in H3.
unfold pl_essence in |- *.
simpl in H3.
elim (le_or_lt (pl_card la + pl_card p) x).
intro.
exact H15.
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
exact (le_trans _ _ _ (lt_le_S _ _ H15) (plus_le_compat (pl_card la) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))).
exact H3.
exact H14.
right.
elim (nat_sum x).
intro.
rewrite H15.
reflexivity.
intros.
elim H15.
intros.
rewrite H16.
induction p as [a1 p1 Hrecp1 p0 Hrecp0| ]; reflexivity.
elim (H (pl_produit_1 ls x (prec_cons x0 x1 x2)) a n0 x).
intros.
rewrite <- H12 in H2.
rewrite H9 in H16.
rewrite H9 in H2.
exact (H16 H2).
unfold pl_essence in |- *.
unfold pl_essence in H3.
rewrite H5 in H3.
simpl in H3.
elim (le_or_lt (pl_card la + pl_card p) x).
intro.
exact H16.
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
exact (le_trans _ _ _ (lt_le_S _ _ H16) (plus_le_compat (pl_card la) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))).
exact H3.
exact H14.
left.
rewrite <- H9.
apply (H0 (S n0) x H15).
rewrite H12.
exact H2.
unfold pl_essence in |- *.
unfold pl_essence in H3.
rewrite H5 in H3.
simpl in H3.
elim (le_or_lt (pl_card ls + pl_card p) x); intro.
exact H16.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
exact (le_trans _ _ _ (lt_le_S _ _ H16) (plus_le_compat (pl_card ls) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_r _ _) (le_n_n _))).
exact H3.
Admitted.

Lemma pl_tl_length_prod_5 : forall p p' : prec_list, pl_tl_length_prod_def_0 p p' /\ pl_tl_length_prod_def_1 p p'.
Proof.
Admitted.

Lemma pl_tl_length_prod : forall (pl0 pl1 : prec_list) (n : nat), pl_tl_length pl0 n -> pl_tl_length pl1 n -> pl_tl_length (pl_produit pl0 pl1) n.
Proof.
intros.
elim (pl_tl_length_prod_5 pl0 pl1).
intros.
unfold pl_produit in |- *.
Admitted.

Lemma pl_produit_path_incl_0 : forall (n : nat) (a : ad) (la pl l : prec_list) (plp : pl_path), pl_path_incl plp l -> plp <> pl_path_nil -> pl_essence la pl <= n -> pl_path_incl plp (pl_produit_0 a la pl n l).
Proof.
simple induction n.
intros.
elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 la pl) H1)).
intros.
induction pl as [a0 pl1 Hrecpl1 pl0 Hrecpl0| ].
replace (pl_produit_0 a la (prec_cons a0 pl1 pl0) (S n0) l) with (prec_cons (iad_conv a a0) (pl_produit_1 la n0 pl1) (pl_produit_0 a la pl0 n0 l)).
apply (pl_path_incl_next plp (iad_conv a a0) (pl_produit_1 la n0 pl1) (pl_produit_0 a la pl0 n0 l)).
apply (H a la pl0 l plp H0 H1).
unfold pl_essence in |- *.
unfold pl_essence in H2.
elim (le_or_lt (pl_card la + pl_card pl0) n0).
intro.
exact H3.
intro.
simpl in H2.
cut (pl_card la + S (S (pl_card pl0)) <= pl_card la + S (pl_card pl1 + pl_card pl0)).
intro.
cut (pl_card la + S (S (pl_card pl0)) <= S n0).
intros.
cut (pl_card la + S (S (pl_card pl0)) = S (S (pl_card la + pl_card pl0))).
intro.
rewrite H6 in H5.
elim (le_Sn_n _ (le_trans _ _ _ (le_trans _ _ _ (le_n_S _ _ (le_n_S _ _ (lt_le_S _ _ H3))) H5) (le_n_Sn (S n0)))).
rewrite <- (plus_Snm_nSm (pl_card la) (S (pl_card pl0))).
simpl in |- *.
rewrite <- (plus_Snm_nSm (pl_card la) (pl_card pl0)).
simpl in |- *.
reflexivity.
exact (le_trans _ _ _ H4 H2).
apply (plus_le_compat (pl_card la) (pl_card la) (S (S (pl_card pl0))) (S (pl_card pl1 + pl_card pl0))).
exact (le_n_n _).
apply (le_n_S (S (pl_card pl0)) (pl_card pl1 + pl_card pl0)).
exact (plus_le_compat 1 (pl_card pl1) (pl_card pl0) (pl_card pl0) (pl_card_0 pl1) (le_n_n _)).
exact H1.
reflexivity.
simpl in |- *.
Admitted.

Lemma pl_path_product_n : forall (n : nat) (p0 p1 : pl_path), pl_path_length p0 = n -> pl_path_length p1 = n -> pl_path_length (pl_path_product p0 p1) = n.
Proof.
simple induction n.
intros.
induction p0 as [| a p0 Hrecp0].
induction p1 as [| a p1 Hrecp1].
simpl in |- *.
reflexivity.
inversion H0.
inversion H.
intros.
induction p0 as [| a p0 Hrecp0].
inversion H0.
induction p1 as [| a0 p1 Hrecp1].
inversion H1.
simpl in |- *.
simpl in H0.
simpl in H1.
inversion H0.
inversion H1.
rewrite H3.
rewrite (H p0 p1 H3 H4).
Admitted.

Lemma pl_produit_path_incl_inj : forall (plp0 plp1 plp2 plp3 : pl_path) (n : nat), pl_path_length plp0 = n -> pl_path_length plp1 = n -> pl_path_length plp2 = n -> pl_path_length plp3 = n -> pl_path_product plp0 plp1 = pl_path_product plp2 plp3 -> plp0 = plp2 /\ plp1 = plp3.
Proof.
simple induction plp0.
simple induction plp1.
simple induction plp2.
simple induction plp3.
intros.
split; reflexivity.
intros.
simpl in H2.
rewrite <- H2 in H3.
simpl in H3.
inversion H3.
intros.
simpl in H0.
rewrite <- H0 in H2.
simpl in H2.
inversion H2.
intros.
simpl in H0.
rewrite <- H0 in H1.
simpl in H1.
inversion H1.
intros.
induction plp1 as [| a0 plp1 Hrecplp1].
simpl in H0.
simpl in H1.
rewrite <- H1 in H0.
inversion H0.
induction plp2 as [| a1 plp2 Hrecplp2].
simpl in H2.
rewrite <- H2 in H0.
simpl in H0.
inversion H0.
induction plp3 as [| a2 plp3 Hrecplp3].
simpl in H3.
rewrite <- H3 in H0.
simpl in H0.
inversion H0.
simpl in H4.
inversion H4.
elim (iad_conv_inj _ _ _ _ H6).
intros.
rewrite H5.
rewrite H8.
elim (nat_sum n).
intros.
rewrite H9 in H0.
simpl in H0.
inversion H0.
intros.
elim H9.
intros.
rewrite H10 in H0.
rewrite H10 in H1.
rewrite H10 in H2.
rewrite H10 in H3.
simpl in H0.
simpl in H1.
simpl in H2.
simpl in H3.
inversion H0.
inversion H1.
inversion H2.
inversion H3.
elim (H plp1 plp2 plp3 x H12 H13 H14 H15 H7).
intros.
rewrite H11.
rewrite H16.
Admitted.

Lemma pl_produit_path_incl_1_0 : forall p : prec_list, pl_produit_path_incl_def_0 p prec_empty.
Proof.
unfold pl_produit_path_incl_def_0 in |- *.
intros.
Admitted.

Lemma pl_produit_path_incl_1_1 : forall p : prec_list, pl_produit_path_incl_def_1 p prec_empty.
Proof.
unfold pl_produit_path_incl_def_1 in |- *.
intros.
inversion H1.
inversion H2.
rewrite <- H6 in H0.
inversion H0.
rewrite <- H5 in H.
inversion H.
simpl in |- *.
elim (nat_sum m).
intros.
rewrite H8.
simpl in |- *.
exact pl_path_incl_nil.
intros.
elim H8.
intros.
rewrite H9.
simpl in |- *.
Admitted.

Lemma pl_produit_path_incl_1_2 : forall p : prec_list, pl_produit_path_incl_def_1 prec_empty p.
Proof.
unfold pl_produit_path_incl_def_1 in |- *.
intros.
inversion H0.
rewrite <- H5 in H2.
inversion H2.
rewrite <- H4 in H1.
inversion H1.
inversion H.
simpl in |- *.
elim (nat_sum m); intros.
rewrite H8.
simpl in |- *.
exact pl_path_incl_nil.
elim H8.
intros.
rewrite H9.
simpl in |- *.
Admitted.

Lemma pl_produit_path_incl_1_3 : forall (a : ad) (la ls p : prec_list), pl_produit_path_incl_def_0 p ls -> pl_produit_path_incl_def_1 p la -> pl_produit_path_incl_def_0 p (prec_cons a la ls).
Proof.
unfold pl_produit_path_incl_def_1 in |- *.
unfold pl_produit_path_incl_def_0 in |- *.
intros.
elim (nat_sum m); intros.
rewrite H6 in H5.
elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 p (prec_cons a la ls)) H5)).
elim H6.
intros.
rewrite H7.
replace (pl_produit_0 a0 p (prec_cons a la ls) (S x) l) with (prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)).
inversion H3.
inversion H1.
simpl in |- *.
apply (pl_path_incl_cons (pl_path_product plp2 plp) (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)).
apply (H0 n x plp2 plp H15 H2 H10).
inversion H4.
exact H19.
exact H20.
rewrite H7 in H5.
unfold pl_essence in |- *.
unfold pl_essence in H5.
elim (le_or_lt (pl_card p + pl_card la) x); intros.
exact H18.
cut (S (pl_card la) <= pl_card (prec_cons a la ls)).
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (pl_card p + S (pl_card la)) (S x)).
rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la)).
simpl in |- *.
exact (le_n_S _ _ (lt_le_S _ _ H18)).
exact (le_trans _ _ _ (plus_le_compat (pl_card p) (pl_card p) (S (pl_card la)) (pl_card (prec_cons a la ls)) (le_n_n _) H19) H5).
simpl in |- *.
exact (le_n_S (pl_card la) (pl_card la + pl_card ls) (le_plus_l (pl_card la) (pl_card ls))).
inversion H16.
elim (H18 (sym_eq H19)).
apply (pl_path_incl_next (pl_path_product plp0 plp1) (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)).
apply (H n x plp0 plp1 a0 l H1 H2).
exact H11.
inversion H4.
rewrite <- H17 in H11.
inversion H11.
elim (H13 (sym_eq H19)).
exact H19.
rewrite H7 in H5.
unfold pl_essence in |- *.
unfold pl_essence in H5.
elim (le_or_lt (pl_card p + pl_card ls) x).
intro.
exact H14.
intro.
simpl in H5.
rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)) in H5.
simpl in H5.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card p + (pl_card la + pl_card ls))) (S x)).
apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))).
exact (le_trans _ _ _ (lt_le_S _ _ H14) (plus_le_compat (pl_card p) (pl_card p) (pl_card ls) (pl_card la + pl_card ls) (le_n_n _) (le_plus_r (pl_card la) (pl_card ls)))).
exact H5.
inversion H1.
induction plp1 as [| a3 plp1 Hrecplp1].
elim (H13 (refl_equal _)).
simpl in |- *.
intro.
inversion H19.
inversion H17.
elim (H19 (sym_eq H20)).
Admitted.

Lemma pl_produit_path_incl_1_4 : forall (a : ad) (la ls p : prec_list), pl_produit_path_incl_def_0 la p -> pl_produit_path_incl_def_1 ls p -> pl_produit_path_incl_def_1 (prec_cons a la ls) p.
Proof.
unfold pl_produit_path_incl_def_0 in |- *.
unfold pl_produit_path_incl_def_1 in |- *.
intros.
induction p as [a0 p1 Hrecp1 p0 Hrecp0| ].
clear Hrecp0.
clear Hrecp1.
elim (nat_sum m).
intro.
rewrite H6 in H5.
elim (le_Sn_O 0 (le_trans _ _ _ (pl_ess_invar_0 (prec_cons a la ls) (prec_cons a0 p1 p0)) H5)).
intros.
elim H6.
intros.
rewrite H7.
replace (pl_produit_1 (prec_cons a la ls) (S x) (prec_cons a0 p1 p0)) with (pl_produit_0 a la (prec_cons a0 p1 p0) x (pl_produit_1 ls x (prec_cons a0 p1 p0))).
inversion H1.
elim (nat_sum n).
intros.
rewrite H13 in H2.
inversion H2.
intros.
elim H13.
intros.
rewrite <- H8.
rewrite H9.
rewrite H8.
apply (H x0 x plp0 plp1 a (pl_produit_1 ls x (prec_cons a0 p1 p0))).
rewrite H8 in H9.
rewrite <- H9.
exact (pl_path_incl_cons plp a la prec_empty H10).
rewrite H14 in H2.
inversion H2.
exact H16.
exact H17.
exact H3.
rewrite H14 in H4.
exact H4.
unfold pl_essence in |- *.
unfold pl_essence in H5.
elim (le_or_lt (pl_card la + pl_card (prec_cons a0 p1 p0)) x).
intro.
exact H15.
intro.
rewrite H7 in H5.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (pl_card (prec_cons a la ls) + pl_card (prec_cons a0 p1 p0)) (S x)).
simpl in |- *.
simpl in H15.
apply (le_n_S (S x) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))).
apply (le_trans (S x) (pl_card la + S (pl_card p1 + pl_card p0)) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))).
exact (lt_le_S _ _ H15).
exact (plus_le_compat (pl_card la) (pl_card la + pl_card ls) (S (pl_card p1 + pl_card p0)) (S (pl_card p1 + pl_card p0)) (le_plus_l (pl_card la) (pl_card ls)) (le_n_n _)).
exact H5.
apply (pl_produit_path_incl_0 x a la (prec_cons a0 p1 p0) (pl_produit_1 ls x (prec_cons a0 p1 p0)) (pl_path_product plp0 plp1)).
apply (H0 n x plp0 plp1).
exact H11.
inversion H2.
rewrite <- H17 in H11.
inversion H11.
rewrite <- H19 in H13.
elim (H13 (refl_equal pl_path_nil)).
exact H19.
exact H3.
exact H4.
rewrite H7 in H5.
unfold pl_essence in |- *.
unfold pl_essence in H5.
elim (le_or_lt (pl_card ls + pl_card (prec_cons a0 p1 p0)) x).
intro.
exact H14.
intro.
simpl in H14.
simpl in H5.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))).
exact (le_trans (S x) (pl_card ls + S (pl_card p1 + pl_card p0)) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0)) (lt_le_S x (pl_card ls + S (pl_card p1 + pl_card p0)) H14) (plus_le_compat (pl_card ls) (pl_card la + pl_card ls) (S (pl_card p1 + pl_card p0)) (S (pl_card p1 + pl_card p0)) (le_plus_r (pl_card la) (pl_card ls)) (le_n_n _))).
exact H5.
inversion H3.
inversion H1.
simpl in |- *.
intro.
inversion H24.
induction plp0 as [| a4 plp0 Hrecplp0].
elim (H24 (refl_equal pl_path_nil)).
simpl in |- *.
intro.
inversion H25.
induction plp0 as [| a3 plp0 Hrecplp0].
elim (H13 (refl_equal _)).
induction plp1 as [| a4 plp1 Hrecplp1].
elim (H19 (refl_equal _)).
simpl in |- *.
intro.
inversion H20.
rewrite H7 in H5.
unfold pl_essence in H5.
unfold pl_essence in |- *.
simpl in H5.
simpl in |- *.
elim (le_or_lt (pl_card la + S (pl_card p1 + pl_card p0)) x).
intro.
exact H14.
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0)))).
apply (le_n_S (S x) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0))).
exact (le_trans (S x) (pl_card la + S (pl_card p1 + pl_card p0)) (pl_card la + pl_card ls + S (pl_card p1 + pl_card p0)) (lt_le_S _ _ H14) (plus_le_compat (pl_card la) (pl_card la + pl_card ls) (S (pl_card p1 + pl_card p0)) (S (pl_card p1 + pl_card p0)) (le_plus_l _ _) (le_n_n _))).
exact H5.
reflexivity.
inversion H4.
rewrite <- H7 in H2.
Admitted.

Lemma pl_produit_path_incl_1 : forall (pl0 pl1 : prec_list) (n m : nat) (plp0 plp1 : pl_path), pl_path_incl plp0 pl0 -> pl_tl_length pl0 n -> pl_path_incl plp1 pl1 -> pl_tl_length pl1 n -> pl_essence pl0 pl1 <= m -> pl_path_incl (pl_path_product plp0 plp1) (pl_produit_1 pl0 m pl1).
Proof.
intros.
elim (pl_produit_path_incl_1_5 pl0 pl1).
intros.
unfold pl_produit_path_incl_def_1 in H5.
Admitted.

Lemma pl_produit_path_incl_2 : forall (pl0 pl1 : prec_list) (n : nat) (plp0 plp1 : pl_path), pl_path_incl plp0 pl0 -> pl_tl_length pl0 n -> pl_path_incl plp1 pl1 -> pl_tl_length pl1 n -> pl_path_incl (pl_path_product plp0 plp1) (pl_produit pl0 pl1).
Proof.
intros.
unfold pl_produit in |- *.
Admitted.

Lemma pl_produit_path_incl_3_0 : forall p : prec_list, pl_produit_path_incl_def_2 p prec_empty.
Proof.
unfold pl_produit_path_incl_def_2 in |- *.
intros.
elim (nat_sum m).
intro.
rewrite H3 in H2.
elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 p prec_empty) H2)).
intros.
elim H3.
intros.
rewrite H4 in H.
simpl in H.
right.
Admitted.

Lemma pl_produit_path_incl_3_1 : forall p : prec_list, pl_produit_path_incl_def_3 p prec_empty.
Proof.
unfold pl_produit_path_incl_def_3 in |- *.
intros.
split with pl_path_nil.
split with pl_path_nil.
split.
elim (nat_sum m).
intro.
rewrite H3 in H.
simpl in H.
inversion H.
reflexivity.
intro.
elim H3.
intros.
rewrite H4 in H.
simpl in H.
induction p as [a p1 Hrecp1 p0 Hrecp0| ]; inversion H; reflexivity.
split.
inversion H1.
rewrite <- H4 in H0.
inversion H0.
exact pl_path_incl_nil.
Admitted.

Lemma pl_produit_path_incl_3_2 : forall p : prec_list, pl_produit_path_incl_def_3 prec_empty p.
Proof.
unfold pl_produit_path_incl_def_3 in |- *.
intros.
split with pl_path_nil.
split with pl_path_nil.
split.
elim (nat_sum m).
intro.
rewrite H3 in H.
simpl in H.
inversion H.
reflexivity.
intros.
elim H3.
intros.
rewrite H4 in H.
simpl in H.
induction p as [a p1 Hrecp1 p0 Hrecp0| ]; simpl in H; inversion H; reflexivity.
split.
exact pl_path_incl_nil.
inversion H0.
rewrite <- H4 in H1.
inversion H1.
Admitted.

Lemma pl_produit_path_incl_3_3 : forall (a : ad) (la ls p : prec_list), pl_produit_path_incl_def_2 p ls -> pl_produit_path_incl_def_3 p la -> pl_produit_path_incl_def_2 p (prec_cons a la ls).
Proof.
unfold pl_produit_path_incl_def_2 in |- *.
unfold pl_produit_path_incl_def_3 in |- *.
intros.
elim (nat_sum m); intros.
rewrite H5 in H4.
elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 p (prec_cons a la ls)) H4)).
elim H5.
intros.
rewrite H6 in H1.
cut (pl_produit_0 a0 p (prec_cons a la ls) (S x) l = prec_cons (iad_conv a0 a) (pl_produit_1 p x la) (pl_produit_0 a0 p ls x l)).
intro.
rewrite H7 in H1.
clear H7.
inversion H1.
elim (H0 n x plp0 H9 H2).
intros.
elim H12.
intros.
left.
split with (pl_path_cons a0 x0).
split with (pl_path_cons a x1).
elim H13.
intros.
elim H15.
intros.
split.
simpl in |- *.
rewrite <- H14.
reflexivity.
split.
exact (pl_path_incl_cons x0 a0 p prec_empty H16).
exact (pl_path_incl_cons x1 a la ls H17).
inversion H3.
exact H13.
exact H14.
unfold pl_essence in |- *.
unfold pl_essence in H4.
rewrite H6 in H4.
simpl in H4.
elim (le_or_lt (pl_card p + pl_card la) x).
intro.
exact H12.
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)).
rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)).
simpl in |- *.
apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))).
exact (le_trans _ _ _ (lt_le_S _ _ H12) (plus_le_compat (pl_card p) (pl_card p) (pl_card la) (pl_card la + pl_card ls) (le_n_n _) (le_plus_l (pl_card la) (pl_card ls)))).
exact H4.
elim (pl_sum ls); intro.
rewrite H13 in H10.
elim (nat_sum x).
intros.
rewrite H14 in H10.
simpl in H10.
inversion H10.
elim (H12 (sym_eq H15)).
intros.
elim H14.
intros.
rewrite H15 in H10.
simpl in H10.
right.
exact H10.
elim (H n x plp a0 l H10 H2).
intros.
elim H14.
intros.
elim H15.
intros.
elim H16.
intros.
elim H18.
intros.
left.
split with x0.
split with x1.
split.
exact H17.
split.
exact H19.
apply (pl_path_incl_next x1 a la ls H20).
intro.
rewrite H21 in H17.
induction x0 as [| a2 x0 Hrecx0]; inversion H17; rewrite H17 in H12; elim (H12 (refl_equal _)).
intro.
right.
exact H14.
inversion H3.
rewrite <- H17 in H13.
elim H13.
intros.
elim H19.
intros.
elim H20.
intros.
inversion H21.
exact H19.
unfold pl_essence in |- *.
unfold pl_essence in H4.
rewrite H6 in H4.
simpl in H4.
elim (le_or_lt (pl_card p + pl_card ls) x); intro.
exact H14.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (pl_card p + S (pl_card la + pl_card ls)) (S x)).
rewrite <- (plus_Snm_nSm (pl_card p) (pl_card la + pl_card ls)).
simpl in |- *.
apply (le_n_S (S x) (pl_card p + (pl_card la + pl_card ls))).
exact (le_trans (S x) (pl_card p + pl_card ls) (pl_card p + (pl_card la + pl_card ls)) (lt_le_S _ _ H14) (plus_le_compat (pl_card p) (pl_card p) (pl_card ls) (pl_card la + pl_card ls) (le_n_n _) (le_plus_r _ _))).
exact H4.
Admitted.

Lemma pl_produit_path_incl_3_4 : forall (a : ad) (la ls p : prec_list), pl_produit_path_incl_def_2 la p -> pl_produit_path_incl_def_3 ls p -> pl_produit_path_incl_def_3 (prec_cons a la ls) p.
Proof.
unfold pl_produit_path_incl_def_3 in |- *.
unfold pl_produit_path_incl_def_2 in |- *.
intros.
elim (nat_sum m).
intro.
rewrite H5 in H4.
elim (le_Sn_n 0 (le_trans _ _ _ (pl_ess_invar_0 (prec_cons a la ls) p) H4)).
intros.
elim H5.
intros.
rewrite H6 in H1.
elim (pl_sum p).
intros.
rewrite H7 in H1.
rewrite H7 in H3.
inversion H3.
rewrite <- H9 in H2.
inversion H2.
intros.
cut (pl_produit_1 (prec_cons a la ls) (S x) p = pl_produit_0 a la p x (pl_produit_1 ls x p)).
intro.
rewrite H8 in H1.
clear H8.
inversion H1.
rewrite (pl_product_1 a la p (pl_produit_1 ls x p) x) in H7.
elim H7.
intros.
elim H9.
intros.
elim H11.
intros.
inversion H12.
rewrite H6 in H4.
unfold pl_essence in |- *.
unfold pl_essence in H4.
simpl in H4.
elim (le_or_lt (pl_card la + pl_card p) x).
intro.
exact H9.
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
exact (le_trans _ _ _ (lt_le_S _ _ H9) (plus_le_compat (pl_card la) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))).
exact H4.
exact (sym_eq H10).
elim (nat_sum n).
intro.
rewrite H11 in H2.
inversion H2.
intro.
elim H11.
intros.
rewrite H12 in H2.
elim (H x0 x plp a (pl_produit_1 ls x p) H1).
intros.
elim H13.
intros.
elim H14.
intros.
elim H15.
intros.
elim H17.
intros.
split with x1.
split with x2.
split.
rewrite <- H16.
exact H9.
split.
inversion H18.
exact (pl_path_incl_cons plp1 a la ls H22).
inversion H23.
elim (H25 (sym_eq H26)).
exact H19.
intro.
elim (pl_sum ls).
intro.
rewrite H14 in H13.
induction x as [| x Hrecx]; simpl in H13.
inversion H13.
rewrite <- H15 in H9.
inversion H9.
induction p as [a1 p1 Hrecp1 p0 Hrecp0| ]; inversion H13.
rewrite <- H15 in H9.
inversion H9.
rewrite <- H15 in H9.
inversion H9.
intros.
elim (H0 n x plp H13).
intros.
elim H15.
intros.
elim H16.
intros.
elim H18.
intros.
split with x1.
split with x2.
split.
rewrite <- H17.
exact H9.
split.
apply (pl_path_incl_next x1 a la ls H19).
intro.
rewrite H21 in H17.
induction x2 as [| a1 x2 Hrecx2]; inversion H17; rewrite H17 in H9; inversion H9.
exact H20.
inversion H2.
rewrite <- H18 in H14.
elim H14.
intros.
elim H20.
intros.
elim H21.
intros.
inversion H22.
rewrite H12.
exact H20.
exact H3.
rewrite H6 in H4.
unfold pl_essence in |- *.
unfold pl_essence in H4.
simpl in H4.
elim (le_or_lt (pl_card ls + pl_card p) x).
intro.
exact H15.
intros.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
exact (le_trans _ _ _ (lt_le_S _ _ H15) (plus_le_compat (pl_card ls) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_r _ _) (le_n_n _))).
exact H4.
inversion H2.
exact H14.
exact H15.
rewrite H12 in H3.
exact H3.
unfold pl_essence in |- *.
unfold pl_essence in H4.
rewrite H6 in H4.
simpl in H4.
elim (le_or_lt (pl_card la + pl_card p) x).
intro.
exact H13.
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
apply (le_trans (S x) (pl_card la + pl_card p) (pl_card la + pl_card ls + pl_card p)).
exact (lt_le_S _ _ H13).
exact (plus_le_compat (pl_card la) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _)).
exact H4.
elim (nat_sum n).
intro.
rewrite H12 in H2.
inversion H2.
intro.
elim H12.
intros.
elim (H x0 x plp a (pl_produit_1 ls x p) H1).
intros.
elim H14.
intros.
elim H15.
intros.
elim H16.
intros.
elim H18.
intros.
split with x1.
split with x2.
split.
exact H17.
split.
inversion H19.
exact (pl_path_incl_cons plp1 a la ls H23).
inversion H24.
rewrite <- H27 in H26.
elim (H26 (refl_equal _)).
exact H20.
intro.
elim (pl_sum ls).
intro.
rewrite H15 in H14.
elim (nat_sum x); intro.
rewrite H16 in H14.
inversion H14.
elim (H11 (sym_eq H17)).
elim H16.
intros.
rewrite H17 in H14.
elim (pl_sum p).
intro.
rewrite H18 in H14.
simpl in H14.
inversion H14.
elim (H11 (sym_eq H19)).
intros.
elim H18.
intros.
elim H19.
intros.
elim H20.
intros.
rewrite H21 in H14.
simpl in H14.
inversion H14.
elim (H11 (sym_eq H22)).
intro.
inversion H2.
rewrite <- H19 in H15.
elim H15.
intros.
elim H21.
intros.
elim H22.
intros.
inversion H23.
elim (H0 (S n0) x plp H14 H21).
intros.
elim H22.
intros.
elim H23.
intros.
elim H25.
intros.
split with x1.
split with x2.
split.
exact H24.
split.
apply (pl_path_incl_next x1 a la ls H26).
intro.
rewrite H28 in H24.
induction x2 as [| a2 x2 Hrecx2]; inversion H24; rewrite H24 in H11; elim (H11 (refl_equal pl_path_nil)).
exact H27.
rewrite H18.
exact H3.
unfold pl_essence in |- *.
rewrite H6 in H4.
unfold pl_essence in H4.
simpl in H4.
elim (le_or_lt (pl_card ls + pl_card p) x); intro.
exact H22.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
exact (le_trans _ _ _ (lt_le_S _ _ H22) (plus_le_compat (pl_card ls) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_r _ _) (le_n_n _))).
exact H4.
rewrite H13 in H2.
inversion H2; assumption.
rewrite H13 in H3.
exact H3.
unfold pl_essence in H4.
rewrite H6 in H4.
simpl in H4.
unfold pl_essence in |- *.
elim (le_or_lt (pl_card la + pl_card p) x).
intro.
exact H14.
intro.
elim (le_Sn_n (S x)).
apply (le_trans (S (S x)) (S (pl_card la + pl_card ls + pl_card p)) (S x)).
apply (le_n_S (S x) (pl_card la + pl_card ls + pl_card p)).
exact (le_trans _ _ _ (lt_le_S _ _ H14) (plus_le_compat (pl_card la) (pl_card la + pl_card ls) (pl_card p) (pl_card p) (le_plus_l _ _) (le_n_n _))).
exact H4.
elim H7.
intros.
elim H8; intros.
elim H9.
intros.
rewrite H10.
Admitted.

Lemma pl_produit_path_incl_3_5 : forall p p' : prec_list, pl_produit_path_incl_def_2 p p' /\ pl_produit_path_incl_def_3 p p'.
Proof.
Admitted.

Lemma pl_produit_path_incl_3 : forall (pl0 pl1 : prec_list) (n m : nat) (plp : pl_path), pl_path_incl plp (pl_produit_1 pl0 m pl1) -> pl_tl_length pl0 n -> pl_tl_length pl1 n -> pl_essence pl0 pl1 <= m -> exists plp0 : pl_path, (exists plp1 : pl_path, plp = pl_path_product plp0 plp1 /\ pl_path_incl plp0 pl0 /\ pl_path_incl plp1 pl1).
Proof.
intro.
intro.
elim (pl_produit_path_incl_3_5 pl0 pl1).
intro.
intro.
Admitted.

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

Lemma pl_produit_path_incl_1_5 : forall p p' : prec_list, pl_produit_path_incl_def_0 p p' /\ pl_produit_path_incl_def_1 p p'.
Proof.
exact (indprinciple_pl pl_produit_path_incl_def_0 pl_produit_path_incl_def_1 pl_produit_path_incl_1_0 pl_produit_path_incl_1_1 pl_produit_path_incl_1_2 pl_produit_path_incl_1_3 pl_produit_path_incl_1_4).
