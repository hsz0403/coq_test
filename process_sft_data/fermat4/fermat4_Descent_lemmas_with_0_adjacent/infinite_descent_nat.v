Require Export Wf_nat.
Require Export ZArith.
Open Scope Z_scope.
Definition R_noet (x y : nat * nat) : Prop := ((fst x) + (snd x) < (fst y) + (snd y))%nat.
Definition f (x : nat * nat) := ((fst x) + (snd x))%nat.

Lemma infinite_descent_nat : forall P : nat * nat -> Prop, (forall x : nat * nat, (P x -> exists y : nat * nat, (fst(y) + snd(y) < fst(x) + snd(x))%nat /\ P y)) -> forall x : nat * nat, ~(P x).
Proof.
intros; apply (noetherian (fun x => ~(P x))); red; intros; elim (H z H1); intros; apply (H0 x0); tauto.
