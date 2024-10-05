Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils fol_ops fo_sig fo_terms fo_logic.
Set Implicit Arguments.
Local Reserved Notation "⟪ A ⟫'" (at level 1, format "⟪ A ⟫'").
Local Notation ø := vec_nil.
Section Uniform_arities_to_one.
Variable (Σ : fo_signature) (HΣ : syms Σ -> False) (a : nat) (Ha : forall r, ar_rels Σ r = a).
Definition Σone_rel : fo_signature.
Proof.
exists (rels Σ) unit.
+
exact (fun _ => 0).
+
exact (fun _ => S a).
Defined.
Notation Σ' := Σone_rel.
Notation 𝕋 := (fol_term Σ).
Notation 𝔽 := (fol_form Σ).
Notation 𝕋' := (fol_term Σ').
Notation 𝔽' := (fol_form Σ').
Let convert_t (t : 𝕋) : 𝕋' := match t with | in_var s => in_var s | in_fot s _ => False_rect _ (HΣ s) end.
Let convert_v n (v : vec _ n) := vec_map convert_t v.
Fixpoint Σunif_one_rel (A : 𝔽) : 𝔽' := match A with | ⊥ => ⊥ | fol_atom r v => @fol_atom Σ' tt (in_fot r ø##cast (convert_v v) (Ha _)) | fol_bin b A B => fol_bin b (Σunif_one_rel A) (Σunif_one_rel B) | fol_quant q A => fol_quant q (Σunif_one_rel A) end.
Notation encode := Σunif_one_rel.
Variable X : Type.
Section soundness.
Variable (M : fo_model Σ X) (x0 : X).
Notation X' := (X + rels Σ)%type.
Let fX (x : X') : X := match x with | inl x => x | inr _ => x0 end.
Let vX n (v : vec _ n) := vec_map fX v.
Definition Σunif_one_rel_model : fo_model Σ' X'.
Proof.
split.
+
exact (fun r _ => inr r).
+
exact (fun r v => match vec_head v with | inl _ => False (* arbitrary value here *) | inr r => fom_rels M r (cast (vX (vec_tail v)) (eq_sym (Ha _))) end).
Defined.
Notation M' := Σunif_one_rel_model.
Let convert_env (φ : nat -> X) n : X' := inl (φ n).
Let env_fill (ψ : nat -> X') n : X' := inl (fX (ψ n)).
Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).
Let env_fill_sat_help A ψ x : ⟪encode A⟫' (env_fill x·(env_fill ψ)) <-> ⟪encode A⟫' (env_fill x·ψ).
Proof.
apply fol_sem_ext; intros [] _; auto.
Let env_fill_sat A ψ : ⟪encode A⟫' (env_fill ψ) <-> ⟪encode A⟫' ψ.
Proof.
induction A as [ | r v | b A HA B HB | q A HA ] in ψ |- *; try tauto.
-
simpl; rewrite <- (Ha r), !cast_refl.
unfold vX, convert_v; rewrite !vec_map_map.
apply fol_equiv_ext; f_equal.
apply vec_pos_ext; intros p; rew vec.
generalize (vec_pos v p).
intros []; simpl; auto; exfalso; auto.
-
apply fol_bin_sem_ext; auto.
-
simpl; apply fol_quant_sem_ext; intro; auto.
rewrite <- HA, env_fill_sat_help, HA; tauto.
End soundness.
Section completeness.
Variable (M' : fo_model Σ' X).
Definition Σone_unif_rel_model : fo_model Σ X.
Proof.
split.
+
intros ? _; exfalso; auto.
+
exact (fun r v => fom_rels M' tt (fom_syms M' r ø##cast v (Ha _))).
Defined.
Notation M := Σone_unif_rel_model.
Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).
End completeness.
End Uniform_arities_to_one.

Definition Σone_rel : fo_signature.
Proof.
exists (rels Σ) unit.
+
exact (fun _ => 0).
+
exact (fun _ => S a).
