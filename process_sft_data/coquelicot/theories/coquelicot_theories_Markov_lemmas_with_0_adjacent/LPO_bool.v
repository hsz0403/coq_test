Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Lemma LPO_bool : forall f : nat -> bool, {n | f n = true} + {forall n, f n = false}.
Proof.
intros f.
destruct (LPO (fun n => f n = true)) as [H|H].
simpl.
intros n.
case (f n).
now left.
now right.
now left.
right.
intros n.
now apply Bool.not_true_is_false.
