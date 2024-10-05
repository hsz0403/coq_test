Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export Nat_complements.
Require Export groups.
Require Export rings.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.
Fixpoint multpos (x2 : Z) (n : nat) {struct n} : Z := match n with | O => x2 | S n0 => addZ (multpos x2 n0) x2 end.
Fixpoint multneg (x2 : Z) (n : nat) {struct n} : Z := match n with | O => oppZ x2 | S n0 => addZ (multneg x2 n0) (oppZ x2) end.
Definition multZ (x1 x2 : Z) := match x1 with | OZ => OZ | pos n => multpos x2 n | neg n => multneg x2 n end.

Lemma tech_div32 : forall n q r : nat, S n > r -> pos (n - r) = addZ (pos n) (oppZ (posOZ r)).
intros n q r; elim r.
unfold posOZ in |- *; unfold oppZ in |- *; rewrite (add_OZ (pos n)); elim (minus_n_O n).
reflexivity.
intros y H; unfold posOZ in |- *; unfold oppZ in |- *; symmetry in |- *.
exact (tech_add_pos_neg_posZ n y (gt_S_n y n H0)).
