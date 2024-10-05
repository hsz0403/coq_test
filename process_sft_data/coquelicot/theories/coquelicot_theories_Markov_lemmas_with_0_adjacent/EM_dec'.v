Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Lemma EM_dec' : forall P : Prop, P \/ not P -> {P} + {not P}.
Proof.
intros P HP.
destruct (EM_dec P) as [H|H].
-
left.
now destruct HP.
-
now right.
