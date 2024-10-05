Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Lemma EM_dec : forall P : Prop, {not (not P)} + {not P}.
Proof.
intros P.
set (E := fun x => x = 0 \/ (x = 1 /\ P)).
destruct (completeness E) as [x H].
-
exists 1.
intros x [->|[-> _]].
apply Rle_0_1.
apply Rle_refl.
-
exists 0.
now left.
destruct (Rle_lt_dec 1 x) as [H'|H'].
-
left.
intros HP.
elim Rle_not_lt with (1 := H').
apply Rle_lt_trans with (2 := Rlt_0_1).
apply H.
intros y [->|[_ Hy]].
apply Rle_refl.
now elim HP.
-
right.
intros HP.
apply Rlt_not_le with (1 := H').
apply H.
right.
now split.
