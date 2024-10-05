Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
Require Import Undecidability.FOL.FOL.
From Undecidability.FOL.Reductions Require PCPb_to_FOL PCPb_to_FOL_intu PCPb_to_FOL_class.

Lemma undecidable_FOLstar_valid : undecidable FOL*_valid.
Proof.
apply (undecidability_from_reducibility PCPb_undec).
apply PCPb_to_FOL.valid_star_red.
