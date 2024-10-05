Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Undecidability.PolynomialConstraints.Reductions.FMsetC_SAT_to_LPolyNC_SAT.
Require Import Undecidability.SetConstraints.FMsetC_undec.
Theorem LPolyNC_SAT_undec : undecidable LPolyNC_SAT.
Proof.
apply (undecidability_from_reducibility FMsetC_SAT_undec).
exact FMsetC_SAT_to_LPolyNC_SAT.reduction.
Qed.
Check LPolyNC_SAT_undec.