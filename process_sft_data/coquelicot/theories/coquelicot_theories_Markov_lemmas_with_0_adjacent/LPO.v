Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Theorem LPO : forall P : nat -> Prop, (forall n, P n \/ ~ P n) -> {n : nat | P n} + {forall n, ~ P n}.
Proof.
intros P HP.
destruct (LPO_min P HP) as [[n [Pn _]]|Pn].
left.
now exists n.
now right.
