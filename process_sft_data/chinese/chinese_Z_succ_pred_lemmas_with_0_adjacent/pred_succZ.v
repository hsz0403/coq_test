Require Export Arith.
Require Export Zbase.
Definition succZ (x : Z) := match x return Z with | OZ => (* OZ *) IZ (* pos n *) | pos n => pos (S n) (* neg n *) | neg n => match n return Z with | O => (* O *) OZ (* S m *) | S m => neg m end end.
Definition predZ (x : Z) := match x return Z with | OZ => (* OZ *) neg 0 (* pos n *) | pos n => match n return Z with | O => (* O *) OZ (* S m *) | S m => pos m end (* neg n *) | neg n => neg (S n) end.

Lemma pred_succZ : forall x : Z, predZ (succZ x) = x.
Proof.
intros; pattern x in |- *; elim x.
simpl in |- *; reflexivity.
simpl in |- *; reflexivity.
intros; elim n.
simpl in |- *; reflexivity.
intros; simpl in |- *; reflexivity.
