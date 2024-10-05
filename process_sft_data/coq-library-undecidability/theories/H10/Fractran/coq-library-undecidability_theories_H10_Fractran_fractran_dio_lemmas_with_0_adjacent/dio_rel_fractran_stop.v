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

Lemma dio_rel_fractran_stop l x : 𝔻F x -> 𝔻R (fun ν => fractran_stop l (x ν)).
Proof.
intros Hx.
induction l as [ | (p,q) l IHl ].
+
by dio equiv (fun _ => True).
abstract(intro v; split; auto; intros _ ?; rewrite fractran_step_nil_inv; auto).
+
dio by lemma (fun v => fractan_stop_cons_inv p q l (x v)).
