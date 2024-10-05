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

Lemma ord_total_order: forall alpha beta:Ordinal, alpha < beta \/ alpha == beta \/ alpha > beta.
Proof.
induction alpha.
induction beta.
destruct (IHalpha beta) as [|[|]].
left; apply ord_lt_respects_succ; trivial.
right; left.
split.
apply ord_le_respects_succ; apply H.
apply ord_le_respects_succ; apply H.
right; right.
apply ord_lt_respects_succ; trivial.
destruct (classic (exists i:I, ordS alpha < o i)).
destruct H0 as [i].
left.
apply ord_lt_le_trans with (o i); trivial.
apply ord_le_sup.
destruct (classic (exists i:I, ordS alpha == o i)).
destruct H1 as [i].
right; left.
split.
apply ord_le_trans with (o i).
apply H1.
apply ord_le_sup.
apply ord_sup_minimal.
intro.
destruct (H i0) as [|[|]].
contradiction H0; exists i0; trivial.
apply H2.
apply ord_lt_le; trivial.
assert (forall i:I, ordS alpha > o i).
intros.
destruct (H i) as [|[|]].
contradiction H0; exists i; trivial.
contradiction H1; exists i; trivial.
trivial.
right; right.
apply ord_le_lt_trans with alpha.
apply ord_sup_minimal.
intro.
apply ord_le_respects_succ_converse.
apply H2.
apply ord_le_refl.
induction beta.
case (classic (exists i:I, o i > ordS beta)); intro.
destruct H0 as [i].
right; right.
apply ord_lt_le_trans with (o i); trivial.
apply ord_le_sup.
case (classic (exists i:I, o i == ordS beta)); intro.
right; left.
destruct H1 as [i].
split.
apply ord_sup_minimal.
intro j.
destruct (H j (ordS beta)) as [|[|]].
apply ord_lt_le; trivial.
apply H2.
contradiction H0; exists j; trivial.
apply ord_le_trans with (o i).
apply H1.
apply ord_le_sup.
left.
apply ord_le_respects_succ.
apply ord_sup_minimal.
intro.
destruct (H i (ordS beta)) as [|[|]].
apply ord_le_respects_succ_converse; trivial.
contradiction H1; exists i; trivial.
contradiction H0; exists i; trivial.
case (classic (exists j:I0, ord_sup o < o0 j)); intro.
left.
destruct H1 as [j].
apply ord_lt_le_trans with (o0 j); trivial.
apply ord_le_sup.
case (classic (exists i:I, o i > ord_sup o0)); intro.
destruct H2 as [i].
right; right.
apply ord_lt_le_trans with (o i); trivial.
apply ord_le_sup.
right; left.
split.
apply ord_sup_minimal; intro.
destruct (H i (ord_sup o0)) as [|[|]].
apply ord_lt_le; trivial.
apply H3.
contradiction H2; exists i; trivial.
apply ord_sup_minimal; intro j.
destruct (H0 j) as [|[|]].
contradiction H1; exists j; trivial.
apply H3.
apply ord_lt_le; trivial.
