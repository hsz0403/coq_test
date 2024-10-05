Require Import Classical.
Declare Scope ordinal_scope.
Inductive Ordinal : Type := | ordS : Ordinal -> Ordinal | ord_sup: forall {I:Type}, (I->Ordinal) -> Ordinal.
Inductive ord_le : Ordinal -> Ordinal -> Prop := | ord_le_respects_succ: forall alpha beta:Ordinal, ord_le alpha beta -> ord_le (ordS alpha) (ordS beta) | ord_le_S_sup: forall (alpha:Ordinal) (J:Type) (beta:J->Ordinal) (j:J), ord_le (ordS alpha) (beta j) -> ord_le (ordS alpha) (ord_sup beta) | ord_sup_minimal: forall (I:Type) (alpha:I->Ordinal) (beta:Ordinal), (forall i:I, ord_le (alpha i) beta) -> ord_le (ord_sup alpha) beta.
Definition ord_lt (alpha beta:Ordinal) := ord_le (ordS alpha) beta.
Definition ord_eq (alpha beta:Ordinal) := ord_le alpha beta /\ ord_le beta alpha.
Definition ord_ge (alpha beta:Ordinal) := ord_le beta alpha.
Definition ord_gt (alpha beta:Ordinal) := ord_lt beta alpha.
Open Scope ordinal_scope.
Notation "alpha < beta" := (ord_lt alpha beta) : ordinal_scope.
Notation "alpha <= beta" := (ord_le alpha beta) : ordinal_scope.
Notation "alpha == beta" := (ord_eq alpha beta) (at level 70) : ordinal_scope.
Notation "alpha > beta" := (ord_gt alpha beta) : ordinal_scope.
Notation "alpha >= beta" := (ord_ge alpha beta) : ordinal_scope.
Inductive successor_ordinal : Ordinal->Prop := | intro_succ_ord: forall alpha:Ordinal, successor_ordinal (ordS alpha) | succ_ord_wd: forall alpha beta:Ordinal, successor_ordinal alpha -> alpha == beta -> successor_ordinal beta.
Inductive limit_ordinal : Ordinal->Prop := | intro_limit_ord: forall {I:Type} (alpha:I->Ordinal), (forall i:I, exists j:I, alpha i < alpha j) -> limit_ordinal (ord_sup alpha) | limit_ord_wd: forall alpha beta:Ordinal, limit_ordinal alpha -> alpha == beta -> limit_ordinal beta.

Lemma ord_lt_trans: forall alpha beta gamma:Ordinal, alpha < beta -> beta < gamma -> alpha < gamma.
Proof.
intros.
apply ord_lt_le_trans with beta; trivial; apply ord_lt_le; trivial.
