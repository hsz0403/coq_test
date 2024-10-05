From Undecidability.H10 Require Import H10 H10_undec Dio.dio_single H10p.
From Undecidability.Synthetic Require Import Undecidability.
Require Import Fin.
Local Set Implicit Arguments.
Definition embed_poly n (p : dio_polynomial (Fin.t n) (Fin.t 0)) : dio_polynomial_pfree.
Proof.
induction p.
-
exact (dp_nat_pfree n0).
-
exact (dp_var_pfree (proj1_sig (to_nat v))).
-
inversion p.
-
exact (dp_comp_pfree (if d then do_add_pfree else do_mul_pfree) IHp1 IHp2).
Defined.
Definition embed (x : H10_PROBLEM) : H10p_PROBLEM := let (n, x) := x in let (p, q) := x in (embed_poly p, embed_poly q).
Definition embed_env n (phi : Fin.t n -> nat) : nat -> nat := fun k => match Compare_dec.lt_dec k n with | left H => phi (of_nat_lt H) | _ => 0 end.
Definition cut_env n (phi : nat -> nat) : Fin.t n -> nat := fun i => phi (proj1_sig (to_nat i)).

Lemma embed_env_eval n (p : dio_polynomial (Fin.t n) (Fin.t 0)) nu phi : dp_eval phi nu p = dp_eval_pfree (embed_env phi) (embed_poly p).
Proof.
induction p.
-
reflexivity.
-
cbn.
unfold embed_env.
destruct Compare_dec.lt_dec as [H|H].
+
erewrite of_nat_ext, of_nat_to_nat_inv.
reflexivity.
+
exfalso.
apply H.
apply proj2_sig.
-
inversion p.
-
cbn [dp_eval].
rewrite IHp1, IHp2.
now destruct d.
