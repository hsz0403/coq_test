From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec Compiler_facts Compiler ClosedLAdmissible Compiler_nat_facts.

Lemma L_computable_to_TM_computable k (R : Vector.t nat k -> nat -> Prop) : L_computable R -> TM_computable R.
Proof.
intros.
eapply TM_bool_computable_to_TM_computable.
eapply L_bool_computable_to_TM_bool_computable.
eapply L_computable_to_L_bool_computable.
eapply H.
