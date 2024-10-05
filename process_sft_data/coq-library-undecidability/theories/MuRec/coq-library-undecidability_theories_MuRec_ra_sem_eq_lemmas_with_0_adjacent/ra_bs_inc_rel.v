From Undecidability.Shared.Libs.DLW Require Import utils finite pos vec.
From Undecidability.MuRec Require Import recalg ra_bs recursor minimizer ra_ca.
Set Implicit Arguments.
Set Default Proof Using "Type".
Notation "[| f |]" := (@ra_rel _ f) (at level 0).
Section soundness_and_completeness.
Hint Resolve ra_ca_inc_bs ra_bs_inc_rel ra_rel_inc_ca : core.
End soundness_and_completeness.

Lemma ra_bs_inc_rel k (f : recalg k) v x : [f;v] ~~> x -> [|f|] v x.
Proof.
induction 1 as [ n v | v | v | k v p | k i f gj v w x H1 IH1 H2 | k f g v n x H1 | k f g v n x y H1 IH1 H2 | k f v n w H1 IH1 H2 ]; try reflexivity.
exists w; split; auto; intros; rewrite vec_pos_set; auto.
red; unfold s_rec; simpl; auto.
rewrite ra_rel_fix_rec in IH1 |- *; unfold s_rec in IH1 |- *.
simpl in IH1 |- *; exists x; auto.
rewrite ra_rel_fix_min; unfold s_min; split; auto.
intros y Hy.
exists (vec_pos w (nat2pos Hy)).
generalize (IH1 (nat2pos Hy)).
rewrite pos2nat_nat2pos.
eqgoal; do 2 f_equal.
