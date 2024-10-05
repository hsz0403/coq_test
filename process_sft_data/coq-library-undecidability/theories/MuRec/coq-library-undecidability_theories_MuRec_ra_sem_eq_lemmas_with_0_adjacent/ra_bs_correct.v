From Undecidability.Shared.Libs.DLW Require Import utils finite pos vec.
From Undecidability.MuRec Require Import recalg ra_bs recursor minimizer ra_ca.
Set Implicit Arguments.
Set Default Proof Using "Type".
Notation "[| f |]" := (@ra_rel _ f) (at level 0).
Section soundness_and_completeness.
Hint Resolve ra_ca_inc_bs ra_bs_inc_rel ra_rel_inc_ca : core.
End soundness_and_completeness.

Theorem ra_bs_correct k (f : recalg k) v x : [|f|] v x <-> [f;v] ~~> x.
Proof.
split; auto.
