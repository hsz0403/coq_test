From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec Compiler_facts Compiler ClosedLAdmissible Compiler_nat_facts.

Lemma L_bool_computable_to_TM_bool_computable k (R : Vector.t (list bool) k -> list bool -> Prop) : L_bool_computable R -> TM_bool_computable R.
Proof.
intros H.
eapply TM_bool_computable_hoare'_spec.
-
now apply L_bool_computable_function.
-
now eapply compiler_correct, L_bool_computable_can_closed.
