Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Lemma LPO_notnotexists : forall P : nat -> Prop, (forall n, P n \/ ~P n) -> ~~ (exists n : nat, P n) -> exists n : nat, P n.
Proof.
intros.
apply LPO_notforall.
apply H.
contradict H0.
intros (n,H1).
contradict H1 ; apply H0.
