From Undecidability.Shared.Libs.DLW Require Import utils finite pos vec.
From Undecidability.MuRec Require Import recalg ra_bs recursor minimizer ra_ca.
Set Implicit Arguments.
Set Default Proof Using "Type".
Notation "[| f |]" := (@ra_rel _ f) (at level 0).
Section soundness_and_completeness.
Hint Resolve ra_ca_inc_bs ra_bs_inc_rel ra_rel_inc_ca : core.
End soundness_and_completeness.

Lemma ra_ca_inc_bs k (f : recalg k) v x : (exists n, [f;v] -[n>> x) -> [f;v] ~~> x.
Proof.
intros (n & H); revert H.
induction 1 as [ n v | v | v | k v p | k i f gj v n w q x H1 IH1 H2 IH2 | k f g v n x H1 IH2 | k f g v n p x q y H1 IH1 H2 IH2 | k f v p n w q H1 IH1 H2 IH2 ]; try (constructor; auto; fail).
apply in_ra_bs_comp with w; auto.
apply in_ra_bs_rec_S with x; auto.
apply in_ra_bs_min with w; auto.
