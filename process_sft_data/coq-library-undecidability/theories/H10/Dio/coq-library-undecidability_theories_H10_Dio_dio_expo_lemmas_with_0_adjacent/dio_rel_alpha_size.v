Require Import Arith ZArith List.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac sums rel_iter gcd.
From Undecidability.H10.Matija Require Import alpha expo_diophantine.
From Undecidability.H10.Dio Require Import dio_logic.
Set Implicit Arguments.
Local Notation power := (mscal mult 1).
Local Notation expo := (mscal mult 1).
Local Notation "x ≐ ⌞ n ⌟" := (df_cst x n) (at level 49, no associativity, format "x ≐ ⌞ n ⌟").
Local Notation "x ≐ y" := (df_eq x y) (at level 49, no associativity, format "x ≐ y").
Local Notation "x ≐ y ⨢ z" := (df_add x y z) (at level 49, no associativity, y at next level, format "x ≐ y ⨢ z").
Local Notation "x ≐ y ⨰ z" := (df_mul x y z) (at level 49, no associativity, y at next level, format "x ≐ y ⨰ z").
Local Fact is_digit_eq c q i y : is_digit c q i y <-> y < q /\ exists a b p, c = (a*q+y)*p+b /\ b < p /\ p = power i q.
Proof.
split; intros (H1 & a & b & H2).
+
split; auto; exists a, b, (power i q); repeat split; tauto.
+
destruct H2 as (p & H2 & H3 & H4).
split; auto; exists a, b; subst; auto.

Fact dio_rel_alpha_size : df_size_Z (proj1_sig dio_rel_alpha_example) = 1445%Z.
Proof.
reflexivity.
