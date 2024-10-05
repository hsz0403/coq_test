Require Import List.
From Undecidability.Shared.Libs.DLW.Utils Require Import finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils decidable fol_ops fo_sig fo_terms fo_logic.
Set Implicit Arguments.
Section satisfiability.
Variable (Σ : fo_signature) (e : rels Σ) (E : ar_rels Σ e = 2) (A : fol_form Σ).
Definition fo_form_fin_SAT_in X := exists (M : fo_model Σ X) (_ : finite_t X) (φ : nat -> X), fol_sem M φ A.
Definition fo_form_fin_dec_SAT_in X := exists (M : fo_model Σ X) (_ : finite_t X) (_ : fo_model_dec M) (φ : nat -> X), fol_sem M φ A.
Definition fo_form_fin_dec_eq_SAT_in X := exists (M : fo_model Σ X) (_ : finite_t X) (_ : fo_model_dec M) (_ : forall x y, fom_rels M e (cast (x##y##ø) (eq_sym E)) <-> x = y) (φ : nat -> X), fol_sem M φ A.
Definition fo_form_fin_discr_dec_SAT_in X := exists (_ : discrete X), fo_form_fin_dec_SAT_in X.
Definition fo_form_fin_SAT := ex fo_form_fin_SAT_in.
Definition fo_form_fin_dec_SAT := ex fo_form_fin_dec_SAT_in.
Definition fo_form_fin_dec_eq_SAT := ex fo_form_fin_dec_eq_SAT_in.
Definition fo_form_fin_discr_dec_SAT := ex fo_form_fin_discr_dec_SAT_in.
Fact fo_form_fin_discr_dec_SAT_fin_dec : fo_form_fin_discr_dec_SAT -> fo_form_fin_dec_SAT.
Proof.
intros (X & _ & ?); exists X; trivial.
Fact fo_form_fin_dec_SAT_fin : fo_form_fin_dec_SAT -> fo_form_fin_SAT.
Proof.
intros (X & M & H & _ & ?); exists X, M, H; trivial.
End satisfiability.

Fact fo_form_fin_dec_SAT_fin : fo_form_fin_dec_SAT -> fo_form_fin_SAT.
Proof.
Admitted.

Fact fo_form_fin_discr_dec_SAT_fin_dec : fo_form_fin_discr_dec_SAT -> fo_form_fin_dec_SAT.
Proof.
intros (X & _ & ?); exists X; trivial.
