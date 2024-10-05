Require Import List.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_nat.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.H10 Require Import Dio.dio_single H10.
From Undecidability.MuRec Require Import recalg ra_dio_poly.
Set Default Proof Using "Type".
Section H10_MUREC_HALTING.
Let f : H10_PROBLEM -> MUREC_PROBLEM.
Proof.
intros (n & p & q).
exact (ra_dio_poly_find p q).
Defined.
End H10_MUREC_HALTING.
Check H10_MUREC_HALTING.

Let f : H10_PROBLEM -> MUREC_PROBLEM.
Proof.
intros (n & p & q).
exact (ra_dio_poly_find p q).
