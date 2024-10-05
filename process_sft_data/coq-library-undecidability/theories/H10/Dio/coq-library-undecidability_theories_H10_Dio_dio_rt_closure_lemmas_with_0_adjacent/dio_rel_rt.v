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

Corollary dio_rel_rt x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun ν => exists i, rel_iter R i (x ν) (y ν)).
Proof using HR.
intros; dio auto.
