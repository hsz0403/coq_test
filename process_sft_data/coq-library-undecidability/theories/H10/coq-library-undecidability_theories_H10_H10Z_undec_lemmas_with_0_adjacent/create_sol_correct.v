Require Import Arith ZArith Lia List.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list gcd prime php utils_nat.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.H10.ArithLibs Require Import Zp lagrange.
From Undecidability.H10.Dio Require Import dio_logic dio_single.
From Undecidability.H10 Require Import H10 H10_undec.
From Undecidability.H10 Require Import H10Z.
From Undecidability.H10.ArithLibs Require Import Zp lagrange.
Require Import Undecidability.Synthetic.Definitions.
Set Default Proof Using "Type".
Local Definition inj k n := 4 * n + k.
Section pos_injs.
Fixpoint inj0 {n} (p : pos n) : pos (n * 4).
Proof.
destruct p.
-
exact pos0.
-
exact (pos_right _ (inj0 _ p)).
Defined.
Fixpoint inj1 {n} (p : pos n) : pos (n * 4).
Proof.
destruct p.
-
exact pos1.
-
exact (pos_right _ (inj1 _ p)).
Defined.
Fixpoint inj2 {n} (p : pos n) : pos (n * 4).
Proof.
destruct p.
-
exact pos2.
-
exact (pos_right _ (inj2 _ p)).
Defined.
Fixpoint inj3 {n} (p : pos n) : pos (n * 4).
Proof.
destruct p.
-
exact pos3.
-
exact (pos_right _ (inj3 _ p)).
Defined.
End pos_injs.
Arguments dp_cnst {V P}.
Arguments dp_var {V P}.
Arguments dp_par {V P}.
Arguments dp_comp {V P}.
Module dionat := dio_single.
Notation dp_sq a := (dp_comp do_mul a a).
Notation sq a := (a * a)%Z.
Fixpoint to_Z_poly E n (p : dionat.dio_polynomial (pos n) E) : dio_polynomial (pos (n * 4)) E := match p with | dionat.dp_nat n => dp_cnst (Z.of_nat n) | dionat.dp_var v => dp_add (dp_sq (dp_var (inj3 v))) (dp_add (dp_sq (dp_var (inj2 v))) (dp_add (dp_sq (dp_var (inj1 v))) (dp_sq (dp_var (inj0 v))))) | dionat.dp_par p => dp_par p | dionat.dp_comp o p1 p2 => dp_comp o (to_Z_poly p1) (to_Z_poly p2) end.
Opaque Zmult.
Check H10_H10Z.

Lemma create_sol_correct E (n : nat) (Φ : pos n -> nat) (Φ' : pos (n * 4) -> Z) : (forall i : pos n, Z.of_nat (Φ i) = sq (Φ' (inj3 i)) + sq (Φ' (inj2 i)) + sq (Φ' (inj1 i)) + sq (Φ' (inj0 i)))%Z -> forall p : dionat.dio_polynomial (pos n) E, Z.of_nat (dio_single.dp_eval Φ (fun _ : E => 0) p) = dp_eval Φ' (fun _ : E => 0%Z) (to_Z_poly p).
Proof.
intros H p.
induction p as [ k | v | | [] ]; cbn; auto.
-
rewrite H; ring.
-
rewrite Nat2Z.inj_add; congruence.
-
rewrite Nat2Z.inj_mul; congruence.
