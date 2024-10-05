Require Export Wf_nat.
Require Export ZArith.
Open Scope Z_scope.
Definition R_noet (x y : nat * nat) : Prop := ((fst x) + (snd x) < (fst y) + (snd y))%nat.
Definition f (x : nat * nat) := ((fst x) + (snd x))%nat.

Lemma noetherian : forall P : nat * nat -> Prop, (forall z : nat * nat, (forall y : nat * nat, (fst(y) + snd(y) < fst(z) + snd(z))%nat -> P y) -> P z) -> forall x : nat * nat, P x.
Proof.
intros; generalize (well_founded_ind R_noet_wf P); auto.
