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

Lemma dio_rel_fractran_step l x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun ν => l /F/ x ν → y ν).
Proof.
intros Hx Hy.
induction l as [ | (p,q) l IHl ].
+
by dio equiv (fun _ => False).
abstract (intros v; rewrite fractran_step_nil_inv; split; tauto).
+
Admitted.

Corollary dio_rel_fractran_rt l x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun ν => fractran_compute l (x ν) (y ν)).
Proof.
Admitted.

Lemma dio_rel_fractran_stop l x : 𝔻F x -> 𝔻R (fun ν => fractran_stop l (x ν)).
Proof.
intros Hx.
induction l as [ | (p,q) l IHl ].
+
by dio equiv (fun _ => True).
abstract(intro v; split; auto; intros _ ?; rewrite fractran_step_nil_inv; auto).
+
Admitted.

Theorem FRACTRAN_HALTING_on_diophantine ll x : 𝔻F x -> 𝔻R (fun ν => FRACTRAN_HALTING (ll,x ν)).
Proof.
Admitted.

Corollary FRACTRAN_HALTING_diophantine_0 ll : 𝔻R (fun ν => FRACTRAN_HALTING (ll,ν 0)).
Proof.
Admitted.

Corollary FRACTRAN_HALTING_diophantine l x : 𝔻R (fun _ => FRACTRAN_HALTING (l,x)).
Proof.
Admitted.

Fact power_expo x y : power x y = y^x.
Proof.
induction x as [ | x IHx ]; simpl.
+
rewrite power_0; auto.
+
Admitted.

Let exp_dio n i j : 𝔻F (fun v => exp i (fun2vec j n v)).
Proof.
revert j i; induction n as [ | n IHn ]; intros j i.
+
simpl; dio auto.
+
by dio equiv (fun v => power (v j) (qs i) * exp (S i) (fun2vec (S j) n v)).
Admitted.

Theorem FRACTRAN_HALTING_on_exp_diophantine n l : 𝔻R (fun ν => l /F/ ps 1 * exp 1 (fun2vec 0 n ν) ↓).
Proof.
apply dio_rel_compose with (R := fun x v => l /F/ x ↓); [ dio auto | ].
Admitted.

Theorem FRACTRAN_HALTING_dio_single E l x : { e : dio_single nat E | l /F/ x ↓ <-> dio_single_pred e (fun _ => 0) }.
Proof.
generalize (@FRACTRAN_HALTING_on_diophantine l (fun _ => x)); intros H1.
spec in H1; dio_rel_auto.
destruct dio_rel_single with (1 := H1) as ((p,q) & He).
unfold FRACTRAN_HALTING in He.
exists (dp_inst_par E (fun _ => 0) p, dp_inst_par E (fun _ => 0) q).
rewrite He with (ν := fun _ => 0).
unfold dio_single_pred; simpl.
Admitted.

Fact fractran_exp_diophantine n : 𝔻F (fun ν => ps 1 * exp 1 (fun2vec 0 n ν)).
Proof.
dio auto.
