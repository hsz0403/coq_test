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

Theorem dio_rel_is_seq c q n : 𝔻F c -> 𝔻F q -> 𝔻F n -> 𝔻R (fun ν => is_seq R (c ν) (q ν) (n ν)).
Proof using HR.
intros H1 H2 H3.
unfold is_seq.
apply dio_rel_fall_lt; dio auto.
