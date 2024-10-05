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

Theorem H10_MUREC_HALTING : H10 ⪯ MUREC_HALTING.
Proof.
exists f.
intros (n & p & q); simpl; unfold MUREC_HALTING.
rewrite ra_dio_poly_find_spec; unfold dio_single_pred.
split.
+
intros (phi & Hphi); exists (vec_set_pos phi).
simpl in Hphi; eq goal Hphi; f_equal; apply dp_eval_ext; auto; try (intros; rewrite vec_pos_set; auto; fail); intros j; analyse pos j.
+
intros (v & Hw); exists (vec_pos v).
Admitted.

Let f : H10_PROBLEM -> MUREC_PROBLEM.
Proof.
intros (n & p & q).
exact (ra_dio_poly_find p q).
