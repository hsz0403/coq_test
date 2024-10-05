Require Import Arith ZArith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd sums.
From Undecidability.H10.ArithLibs Require Import Zp.
From Undecidability.H10.Matija Require Import alpha.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation expo := (mscal mult 1).
Section expo_diophantine.
Variables (p q r : nat).
Definition expo_conditions := r = 0 /\ p = 1 \/ q = 0 /\ 0 < r /\ p = 0 \/ (0 < r /\ q <> 0) /\ exists b m a1 a2 a3, (3 < q+4 /\ a1 = alpha_nat (q+4) (1+r)) /\ (3 < b /\ a2 = alpha_nat b r) /\ (3 < b /\ a3 = alpha_nat b (1+r)) /\ b = a1+q*q+2 /\ m + q*q + 1 = b*q /\ p < m /\ rem (p+b*a2) m = rem (q*a2+a3) m.
Let H_q3_q : 0 < q -> q*q+2 <= q*q*q+2*q.
Proof.
intros H.
apply plus_le_compat; try lia.
replace q with (1+(q-1)) at 3 by lia.
rewrite <- mult_assoc, Nat.mul_add_distr_r, Nat.mul_1_l.
apply le_plus_l.
Infix "⊕" := (Zp_plus _) (at level 50, left associativity).
Infix "⊗" := (Zp_mult _) (at level 40, left associativity).
Notation "∸" := (Zp_opp _).
Notation f := (nat2Zp _).
Notation "〚 x 〛" := (f x).
Ltac fold_nat2Zp := repeat match goal with | |- context[nat2Zp _ ?x ⊕ nat2Zp _ ?y] => rewrite <- nat2Zp_plus | |- context[nat2Zp _ ?x ⊗ nat2Zp _ ?y] => rewrite <- nat2Zp_mult | |- context[∸ nat2Zp _ ?x] => fail end.
End expo_diophantine.
Local Hint Resolve expo_sufficiency expo_necessity : core.

Theorem expo_diophantine p q r : p = expo r q <-> expo_conditions p q r.
Proof.
split; auto.
