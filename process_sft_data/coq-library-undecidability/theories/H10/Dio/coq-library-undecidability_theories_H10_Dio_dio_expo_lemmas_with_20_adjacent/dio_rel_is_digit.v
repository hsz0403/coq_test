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

Theorem dio_rel_alpha a b c : 𝔻F a -> 𝔻F b -> 𝔻F c -> 𝔻R (fun ν => 3 < b ν /\ a ν = alpha_nat (b ν) (c ν)).
Proof.
Admitted.

Fact dio_rel_alpha_size : df_size_Z (proj1_sig dio_rel_alpha_example) = 1445%Z.
Proof.
Admitted.

Theorem dio_fun_expo q r : 𝔻F q -> 𝔻F r -> 𝔻F (fun ν => expo (r ν) (q ν)).
Proof.
Admitted.

Lemma dio_rel_is_digit c q i y : 𝔻F c -> 𝔻F q -> 𝔻F i -> 𝔻F y -> 𝔻R (fun ν => is_digit (c ν) (q ν) (i ν) (y ν)).
Proof.
dio by lemma (fun ν => is_digit_eq (c ν) (q ν) (i ν) (y ν)).
