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
Admitted.

Fact dio_rel_power_subst a b (R : nat -> (nat -> nat) -> Prop) : 𝔻F a -> 𝔻F b -> 𝔻R (fun ν => R (ν 0) (fun n => ν (S n))) -> 𝔻R (fun ν => R (power (a ν) (b ν)) ν).
Proof.
intros Ha Hb HR.
by dio equiv (fun v => exists p, p = power (a v) (b v) /\ R p v).
Admitted.

Corollary dio_rel_rt x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun ν => exists i, rel_iter R i (x ν) (y ν)).
Proof using HR.
Admitted.

Lemma dio_rel_rel_iter n x y : 𝔻F n -> 𝔻F x -> 𝔻F y -> 𝔻R (fun ν => rel_iter R (n ν) (x ν) (y ν)).
Proof using HR.
dio by lemma (fun v => rel_iter_seq_equiv R (n v) (x v) (y v)).
