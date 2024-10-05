Require Export Wf_nat.
Require Export ZArith.
Open Scope Z_scope.
Definition R_noet (x y : nat * nat) : Prop := ((fst x) + (snd x) < (fst y) + (snd y))%nat.
Definition f (x : nat * nat) := ((fst x) + (snd x))%nat.

Lemma R_noet_wf : well_founded R_noet.
Proof.
apply (well_founded_lt_compat _ f R_noet); auto.
