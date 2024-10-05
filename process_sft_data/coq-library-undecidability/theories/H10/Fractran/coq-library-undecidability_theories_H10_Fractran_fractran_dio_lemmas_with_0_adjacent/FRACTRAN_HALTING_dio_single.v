Require Import List Arith.
From Undecidability.Shared.Libs Require Import utils_tac utils_list sums rel_iter gcd pos vec.
From Undecidability.FRACTRAN Require Import FRACTRAN fractran_utils prime_seq.
From Undecidability.H10.Dio Require Import dio_logic dio_bounded dio_rt_closure dio_single.
Set Implicit Arguments.
Set Default Proof Using "Type".
Section fractran_dio.
Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).
Let exp_dio n i j : 𝔻F (fun v => exp i (fun2vec j n v)).
Proof.
revert j i; induction n as [ | n IHn ]; intros j i.
+
simpl; dio auto.
+
by dio equiv (fun v => power (v j) (qs i) * exp (S i) (fun2vec (S j) n v)).
abstract (intros v; simpl fun2vec; rewrite exp_cons, power_expo; auto).
Defined.
Fact fractran_exp_diophantine n : 𝔻F (fun ν => ps 1 * exp 1 (fun2vec 0 n ν)).
Proof.
dio auto.
Defined.
End exp_diophantine.
Hint Resolve fractran_exp_diophantine : dio_fun_db.

Theorem FRACTRAN_HALTING_dio_single E l x : { e : dio_single nat E | l /F/ x ↓ <-> dio_single_pred e (fun _ => 0) }.
Proof.
generalize (@FRACTRAN_HALTING_on_diophantine l (fun _ => x)); intros H1.
spec in H1; dio_rel_auto.
destruct dio_rel_single with (1 := H1) as ((p,q) & He).
unfold FRACTRAN_HALTING in He.
exists (dp_inst_par E (fun _ => 0) p, dp_inst_par E (fun _ => 0) q).
rewrite He with (ν := fun _ => 0).
unfold dio_single_pred; simpl.
split; intros (phi & Hphi); exists phi; revert Hphi; repeat rewrite dp_inst_par_eval; auto.
