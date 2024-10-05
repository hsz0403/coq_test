Require Import List Arith.
From Undecidability.Shared.Libs.DLW Require Import utils_tac utils_list sums pos vec subcode sss.
From Undecidability.MinskyMachines Require Import mm_defs.
From Undecidability.FRACTRAN Require Import FRACTRAN mm_fractran prime_seq.
From Undecidability.H10.Fractran Require Import fractran_dio.
From Undecidability.H10.Dio Require Import dio_logic dio_elem dio_single.
From Undecidability.MuRec Require Import recalg ra_utils recomp ra_recomp ra_dio_poly ra_mm ra_simul.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).
Local Notation "l '/F/' x ↓" := (fractran_terminates l x) (at level 70, no associativity).
Local Notation "'⟦' p '⟧'" := (fun φ ν => dp_eval φ ν p).
Local Notation "f ⇓ v" := (ex (@ra_rel _ f v)) (at level 70, no associativity).
Section Various_definitions_of_recursive_enum.
Variable (n : nat) (P : vec nat n -> Prop).
Definition mm_recognisable_n := { m & { M : list (mm_instr (pos (n+m))) | forall v, P v <-> (1,M) /MM/ (1,vec_app v vec_zero) ↓ } }.
Definition mu_recursive_n := { f | forall v, P v <-> f ⇓ v }.
Notation vec2val := (fun v => vec2fun v 0).
Definition dio_rec_form_n := { A | forall v, P v <-> df_pred A (vec2val v) }.
Definition dio_rec_elem_n := { l | forall v, P v <-> exists φ, Forall (dc_eval φ (vec2val v)) l }.
Definition dio_rec_single_n := { m : nat & { p : dio_polynomial (pos m) (pos n) & { q : dio_polynomial (pos m) (pos n) | forall v, P v <-> exists w, ⟦p⟧ (vec_pos w) (vec_pos v) = ⟦q⟧ (vec_pos w) (vec_pos v) } } }.
Local Theorem dio_rec_form_elem : dio_rec_form_n -> dio_rec_elem_n.
Proof.
intros (A & HA).
destruct (dio_formula_elem A) as (l & _ & _ & Hl).
exists l; intros v.
rewrite HA, Hl; tauto.
Local Theorem dio_rec_elem_single : dio_rec_elem_n -> dio_rec_single_n.
Proof.
intros (l & Hl).
destruct (dio_elem_equation l) as (e & _ & H2).
destruct (dio_poly_eq_pos e) as (m & p & q & H3).
set (p' := dp_proj_par n p).
set (q' := dp_proj_par n q).
exists m, p', q'; intros v.
rewrite Hl, <- H2, H3.
unfold dio_single_pred, p', q'; simpl; split.
+
intros (phi & H).
exists (vec_set_pos phi).
rewrite !dp_proj_par_eval.
eq goal H; f_equal; apply dp_eval_ext; auto.
all: intros; rewrite vec_pos_set; auto.
+
intros (w & H).
exists (vec_pos w).
rewrite !dp_proj_par_eval in H; auto.
Local Theorem dio_rec_single_µ_rec : dio_rec_single_n -> mu_recursive_n.
Proof.
intros (m & p & q & H).
exists (ra_dio_poly_find p q).
intros v; rewrite H, ra_dio_poly_find_spec; tauto.
Local Theorem µ_rec_mm_reco : mu_recursive_n -> mm_recognisable_n.
Proof.
intros (f & Hf).
destruct (ra_mm_simulator f) as (m & M & H).
exists (S m), M; intro.
rewrite Hf, H; tauto.
Section mm_reco_dio_form.
Variable (HP : mm_recognisable_n).
Let FRACTRAN : { l | forall v, P v <-> l /F/ ps 1 * exp 1 v ↓ }.
Proof.
destruct HP as (m & Q & HQ).
destruct mm_fractran_n with (P := Q) as (l & _ & Hl).
exists l.
intros x; rewrite HQ, Hl.
rewrite exp_app, exp_zero, Nat.mul_1_r; tauto.
Local Theorem mm_reco_dio_form : dio_rec_form_n.
Proof using HP.
destruct FRACTRAN as (Q & HQ).
clear FRACTRAN HP.
destruct FRACTRAN_HALTING_on_exp_diophantine with n Q as (A & HA); auto.
exists A; intros v.
rewrite HQ, HA, fun2vec_vec2fun; tauto.
End mm_reco_dio_form.
End Various_definitions_of_recursive_enum.
Local Hint Resolve dio_rec_form_elem dio_rec_elem_single dio_rec_single_µ_rec µ_rec_mm_reco mm_reco_dio_form : core.
Local Notation ø := vec_nil.
Section Various_definitions_of_recursive_enum_1.
Variable (P : nat -> Prop).
Definition mm_recognisable := { m & { M : list (mm_instr (pos (S m))) | forall x, P x <-> (1,M) /MM/ (1,x##vec_zero) ↓ } }.
Definition mu_recursive := { f | forall x, P x <-> f ⇓ (x##ø) }.
Definition dio_rec_single := { m : nat & { p : dio_polynomial (pos m) (pos 1) & { q : dio_polynomial (pos m) (pos 1) | forall x, P x <-> exists w, ⟦p⟧ (vec_pos w) (fun _ => x) = ⟦q⟧ (vec_pos w) (fun _ => x) } } }.
Definition fractran_recognisable := { l | forall x, P x <-> l /F/ 5*7^x ↓ }.
Local Theorem µ_rec_mm_reco_1 : mu_recursive -> mm_recognisable.
Proof.
intros H.
destruct µ_rec_mm_reco with (P := fun v : vec _ 1 => P (vec_head v)) as (m & M & HM).
+
destruct H as (f & Hf); exists f.
intros v; vec split v with x; vec nil v; auto.
+
exists m, M; intros x; rewrite (HM (x##ø)).
rewrite vec_app_cons, vec_app_nil; tauto.
Local Theorem mm_reco_fractran_1 : mm_recognisable -> fractran_recognisable.
Proof.
intros (m & M & HM).
destruct mm_fractran with (P := M) as (l & Hl).
exists l; intro; rewrite HM, Hl, ps_1, qs_1; tauto.
Local Theorem fractran_dio_rec_single_1 : fractran_recognisable -> dio_rec_single.
Proof.
intros (l & Hl).
destruct (FRACTRAN_HALTING_on_exp_diophantine 1 l) as (A & HA).
simpl fun2vec in HA; unfold exp in HA.
destruct dio_rec_elem_single with (P := fun v : vec _ 1 => P (vec_head v)) as (m & p & q & H).
+
apply dio_rec_form_elem.
exists A.
intros v; vec split v with x; vec nil v; simpl.
rewrite Hl, HA, <- qs_1, <- ps_1.
unfold vec2fun; simpl.
rewrite mult_1_r; tauto.
+
exists m, p, q; intros x.
rewrite (H (x##ø)).
apply exists_equiv; intros v.
apply equal_equiv; f_equal; apply dp_eval_ext; auto.
all: intros i; analyse pos i; auto.
Local Theorem dio_rec_single_mm_1 : dio_rec_single -> mu_recursive.
Proof.
intros H.
destruct dio_rec_single_µ_rec with (P := fun v : vec _ 1 => P (vec_head v)) as (f & Hf).
+
destruct H as (m & p & q & H).
exists m, p, q.
intros v; vec split v with x; vec nil v.
simpl vec_head; rewrite H.
apply exists_equiv; intros w.
apply equal_equiv; f_equal; apply dp_eval_ext; auto.
all: intros i; analyse pos i; auto.
+
exists f; intros x; apply (Hf (_##ø)).
End Various_definitions_of_recursive_enum_1.
Local Hint Resolve µ_rec_mm_reco_1 mm_reco_fractran_1 fractran_dio_rec_single_1 dio_rec_single_mm_1 : core.
Check DPRM_1.

Let FRACTRAN : { l | forall v, P v <-> l /F/ ps 1 * exp 1 v ↓ }.
Proof.
destruct HP as (m & Q & HQ).
destruct mm_fractran_n with (P := Q) as (l & _ & Hl).
exists l.
intros x; rewrite HQ, Hl.
Admitted.

Theorem DPRM_1 (P : nat -> Prop) : (mm_recognisable P -> fractran_recognisable P) * (fractran_recognisable P -> dio_rec_single P) * (dio_rec_single P -> mu_recursive P) * (mu_recursive P -> mm_recognisable P).
Proof.
Admitted.

Theorem DPRM_n n (R : vec nat n -> Prop) : (mm_recognisable_n R -> dio_rec_form_n R) * (dio_rec_form_n R -> dio_rec_elem_n R) * (dio_rec_elem_n R -> dio_rec_single_n R) * (dio_rec_single_n R -> mu_recursive_n R) * (mu_recursive_n R -> mm_recognisable_n R).
Proof.
lsplit 4; auto.
