Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Lemma LPO_notforall : forall P : nat -> Prop, (forall n, P n \/ ~P n) -> (~ forall n : nat, ~ P n) -> exists n : nat, P n.
Proof.
intros.
destruct (LPO P H).
destruct s as (n,H1) ; exists n ; apply H1.
contradict H0 ; apply n.
