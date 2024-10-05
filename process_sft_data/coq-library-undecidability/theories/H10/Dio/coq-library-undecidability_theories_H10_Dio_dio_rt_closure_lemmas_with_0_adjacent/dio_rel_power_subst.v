Require Import Arith List Bool.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list rel_iter sums.
From Undecidability.H10.Dio Require Import dio_logic dio_expo dio_bounded.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation power := (mscal mult 1).
Section df_seq.
Variable (R : nat -> nat -> Prop) (HR : 𝔻R (fun ν => R (ν 1) (ν 0))).
End df_rel_iter_rt.
Hint Resolve dio_rel_rel_iter dio_rel_rt : dio_rel_db.

Fact dio_rel_power_subst a b (R : nat -> (nat -> nat) -> Prop) : 𝔻F a -> 𝔻F b -> 𝔻R (fun ν => R (ν 0) (fun n => ν (S n))) -> 𝔻R (fun ν => R (power (a ν) (b ν)) ν).
Proof.
intros Ha Hb HR.
by dio equiv (fun v => exists p, p = power (a v) (b v) /\ R p v).
abstract(intros v; split; eauto; intros (? & ? & ?); subst; auto).
