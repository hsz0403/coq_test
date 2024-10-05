Require Import List Arith Lia Max.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import env mm_defs mme_defs mme_utils.
From Undecidability.MuRec Require Import recalg ra_mm_env.
Set Implicit Arguments.
Set Default Proof Using "Type".
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "i /e/ s '-1>' t" := (mm_sss_env eq_nat_dec i s t) (at level 70, no associativity).
Local Notation "P /e/ s ->> t" := (sss_compute (mm_sss_env eq_nat_dec) P s t) (at level 70, no associativity).
Local Notation "P /e/ s ~~> t" := (sss_output (mm_sss_env eq_nat_dec) P s t) (at level 70, no associativity).
Local Notation "P /e/ s -[ k ]-> t" := (sss_steps (mm_sss_env eq_nat_dec) P k s t) (at level 70, no associativity).
Local Notation "P /e/ s ↓" := (sss_terminates (mm_sss_env eq_nat_dec) P s) (at level 70, no associativity).
Local Notation "i /v/ s '-1>' t" := (@mm_sss _ i s t) (at level 70, no associativity).
Local Notation "P /v/ s ->> t" := (sss_compute (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P /v/ s ~~> t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P /v/ s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t) (at level 70, no associativity).
Local Notation "P /v/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).
Local Notation " e ⇢ x " := (@get_env _ _ e x).
Local Notation " e ⦃ x ⇠ v ⦄ " := (@set_env _ _ eq_nat_dec e x v).
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).
Section mm_nat_pos.
Definition mm_var_map (X Y : Set) (f : X -> Y) (i : mm_instr X) := match i with | INC x => INC (f x) | DEC x p => DEC (f x) p end.
Definition mm_instr_var X (i : mm_instr X) := match i with | INC x => x | DEC x _ => x end.
Definition mm_linstr_vars X := map (@mm_instr_var X).
Definition mm_pos_nat n := map (mm_var_map (@pos2nat n)).
Definition mm_nat_pos_full n l : Forall (fun x => x < n) (mm_linstr_vars l) -> { m | l = @mm_pos_nat n m }.
Proof.
induction l as [ | [ x | x p ] l IHl ]; simpl; intros H.
{
exists nil; auto.
}
1,2: rewrite Forall_cons_inv in H; destruct H as [ H1 H2 ]; destruct (IHl H2) as (m & Hm).
+
exists (INC (nat2pos H1) :: m); simpl; f_equal; auto; f_equal.
rewrite pos2nat_nat2pos; auto.
+
exists (DEC (nat2pos H1) p :: m); simpl; f_equal; auto; f_equal.
rewrite pos2nat_nat2pos; auto.
Definition mm_nat_bound l := S (lmax (mm_linstr_vars l)).
Fact mm_nat_bound_spec l : Forall (fun x => x < mm_nat_bound l) (mm_linstr_vars l).
Proof.
cut (Forall (fun x => x <= lmax (mm_linstr_vars l)) (mm_linstr_vars l)).
+
apply Forall_impl; intros; unfold mm_nat_bound; lia.
+
apply lmax_spec; auto.
Definition mm_nat_pos n l : mm_nat_bound l <= n -> { m | l = @mm_pos_nat n m }.
Proof.
intros H; apply mm_nat_pos_full.
generalize (mm_nat_bound_spec l).
apply Forall_impl; intros; lia.
End mm_nat_pos.
Section mm_pos_nat_sem.
Variable (n : nat).
Implicit Types (e : nat -> nat) (v : vec nat n).
Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew env.
Notation "v '⋈' e" := (forall p, vec_pos v p = e⇢pos2nat p) (at level 70, no associativity).
Fact sss_mm_pos_nat rho st1 st2 e1 : snd st1 ⋈ e1 -> rho /v/ st1 -1> st2 -> exists e2, snd st2 ⋈ e2 /\ mm_var_map (@pos2nat n) rho /e/ (fst st1,e1) -1> (fst st2,e2).
Proof.
revert st1 st2; intros (j1,v1) (j2,v2); simpl.
intros H1 H2.
destruct rho as [ x | x p ]; simpl in *; [ | case_eq (vec_pos v1 x); [ intros He1 | intros q Hq ] ].
-
exists (e1⦃pos2nat x ⇠ S (e1⇢pos2nat x)⦄).
apply mm_sss_INC_inv in H2.
destruct H2 as (? & ?); subst; split.
2: constructor.
intros p.
destruct (pos_eq_dec x p) as [ -> | C ]; rew vec; rew env.
rewrite H1; assert (pos2nat x <> pos2nat p); rew env.
contradict C; revert C; apply pos2nat_inj.
-
exists e1.
apply mm_sss_DEC0_inv in H2; destruct H2; subst; auto.
split; auto; constructor; rewrite <- H1; auto.
-
exists (e1⦃pos2nat x ⇠ q⦄).
apply mm_sss_DEC1_inv with (1 := Hq) in H2.
destruct H2; subst; split.
2: constructor; rewrite <- H1; auto.
intros j.
destruct (pos_eq_dec x j) as [ -> | C ]; rew vec; rew env.
rewrite H1; assert (pos2nat x <> pos2nat j); rew env.
contradict C; revert C; apply pos2nat_inj.
Fact sss_mm_pos_nat_inv rho st1 st2 v1 : v1 ⋈ snd st1 -> mm_var_map (@pos2nat n) rho /e/ st1 -1> st2 -> exists v2, v2 ⋈ snd (st2) /\ rho /v/ (fst st1,v1) -1> (fst st2,v2).
Proof.
revert st1 st2; intros (j1,e1) (j2,e2); simpl.
intros H1 H2.
destruct rho as [ x | x p ]; simpl in *; [ | case_eq (e1⇢pos2nat x); [ intros He1 | intros q Hq ] ].
-
exists (vec_change v1 x (S (vec_pos v1 x))).
apply mm_sss_env_INC_inv in H2.
destruct H2 as (? & ?); subst; split.
2: constructor.
intros p.
destruct (pos_eq_dec x p) as [ -> | C ]; rew vec; rew env.
rewrite H1; assert (pos2nat x <> pos2nat p); rew env.
contradict C; revert C; apply pos2nat_inj.
-
exists v1.
apply mm_sss_env_DEC0_inv in H2; destruct H2; subst; auto.
split; auto; constructor; rewrite H1; auto.
-
exists (vec_change v1 x q).
apply mm_sss_env_DEC1_inv with (1 := Hq) in H2.
destruct H2; subst; split.
2: constructor; rewrite H1; auto.
intros j.
destruct (pos_eq_dec x j) as [ -> | C ]; rew vec; rew env.
rewrite H1; assert (pos2nat x <> pos2nat j); rew env.
contradict C; revert C; apply pos2nat_inj.
Fact sss_steps_mm_pos_nat i P k st1 st2 e1 : snd st1 ⋈ e1 -> (i,P) /v/ st1 -[k]-> st2 -> exists e2, snd st2 ⋈ e2 /\ (i,@mm_pos_nat n P) /e/ (fst st1,e1) -[k]-> (fst st2,e2).
Proof.
intros H1 H2; revert H2 e1 H1.
induction 1 as [ (j,v) | k (j1,v1) (j2,v2) (j3,v3) H1 H2 IH2 ]; simpl; intros e1 H3.
+
exists e1; split; auto; constructor.
+
destruct H1 as (q & l & rho & r & e & [= <- G2] & [= -> <-] & G3).
destruct sss_mm_pos_nat with (2 := G3) (1 := H3) as (e2 & G4 & G5); simpl in *.
destruct IH2 with (1 := G4) as (e3 & G6 & G7).
exists e3; split; auto.
constructor 2 with (st2 := (j2,e2)); auto.
exists i, (mm_pos_nat l), (mm_var_map (@pos2nat _) rho), (mm_pos_nat r), e1; msplit 2; auto.
*
f_equal; subst P; unfold mm_pos_nat; repeat (rewrite map_app; simpl); auto.
*
unfold mm_pos_nat; rew length; auto.
Fact sss_steps_mm_pos_nat_inv i P k st1 st2 v1 : v1 ⋈ snd st1 -> (i,@mm_pos_nat n P) /e/ st1 -[k]-> st2 -> exists v2, v2 ⋈ snd (st2) /\ (i,P) /v/ (fst st1,v1) -[k]-> (fst st2,v2).
Proof.
intros H1 H2; revert H2 v1 H1.
induction 1 as [ (j,e) | k (j1,e1) (j2,e2) (j3,e3) H1 H2 IH2 ]; simpl; intros v1 H3.
+
exists v1; split; auto; constructor.
+
destruct H1 as (q & l & rho & r & e & [= <- G2] & [= -> <-] & G3).
unfold mm_pos_nat in G2; apply map_middle_inv in G2.
destruct G2 as (l' & rho' & r' & G2 & G4 & G5 & G6).
subst rho l r.
destruct sss_mm_pos_nat_inv with (2 := G3) (1 := H3) as (v2 & G7 & G8); simpl in *.
destruct IH2 with (1 := G7) as (v3 & G9 & G10).
exists v3; split; auto.
constructor 2 with (st2 := (j2,v2)); auto.
exists i, l', rho', r', v1; msplit 2; subst; auto; rew length; auto.
End mm_pos_nat_sem.
Section ra_mm_comp.
End ra_mm_comp.

Fact mm_nat_bound_spec l : Forall (fun x => x < mm_nat_bound l) (mm_linstr_vars l).
Proof.
cut (Forall (fun x => x <= lmax (mm_linstr_vars l)) (mm_linstr_vars l)).
+
apply Forall_impl; intros; unfold mm_nat_bound; lia.
+
apply lmax_spec; auto.
