Require Export Arith.
Require Export Zbase.
Definition succZ (x : Z) := match x return Z with | OZ => (* OZ *) IZ (* pos n *) | pos n => pos (S n) (* neg n *) | neg n => match n return Z with | O => (* O *) OZ (* S m *) | S m => neg m end end.
Definition predZ (x : Z) := match x return Z with | OZ => (* OZ *) neg 0 (* pos n *) | pos n => match n return Z with | O => (* O *) OZ (* S m *) | S m => pos m end (* neg n *) | neg n => neg (S n) end.

Lemma tech_succ_posOZ : forall n : nat, succZ (posOZ n) = pos n.
Proof.
intros; elim n; simpl in |- *; reflexivity; simpl in |- *; reflexivity.
