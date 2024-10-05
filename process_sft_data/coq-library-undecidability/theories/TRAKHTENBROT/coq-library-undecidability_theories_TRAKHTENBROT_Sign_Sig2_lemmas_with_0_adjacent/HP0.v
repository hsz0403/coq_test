Require Import List Arith Bool Lia Eqdep_dec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Wf Require Import wf_finite.
From Undecidability.TRAKHTENBROT Require Import notations decidable fol_ops fo_sig fo_terms fo_logic fo_sat membership hfs reln_hfs.
Set Implicit Arguments.
Local Notation ø := vec_nil.
Section Sign_Sig2_encoding.
Variable (n : nat).
Notation Σ2 := (Σrel 2).
Notation Σn := (Σrel n).
Infix "∈" := Σ2_mem.
Infix "≈" := Σ2_equiv.
Infix "⊆" := Σ2_incl.
Fixpoint Σn_Σ2 (d r : nat) (A : fol_form Σn) : fol_form Σ2 := match A with | ⊥ => ⊥ | fol_atom _ v => Σ2_is_tuple_in r (vec_map (@Σrel_var _) v) | fol_bin b A B => fol_bin b (Σn_Σ2 d r A) (Σn_Σ2 d r B) | fol_quant fol_fa A => ∀ 0 ∈ (S d) ⤑ Σn_Σ2 (S d) (S r) A | fol_quant fol_ex A => ∃ 0 ∈ (S d) ⟑ Σn_Σ2 (S d) (S r) A end.
Variable (X : Type) (M2 : fo_model Σ2 X).
Variable (Y : Type) (Mn : fo_model Σn Y).
Let mem a b := fom_rels M2 tt (a##b##ø).
Infix "∈m" := mem (at level 59, no associativity).
Notation P := (fun v => fom_rels Mn tt v).
Variable R : Y -> X -> Prop.
Let HR1 (d r : X) := forall y, exists x, x ∈m d /\ R y x.
Let HR2 (d r : X) := forall x, x ∈m d -> exists y, R y x.
Let HR3 (d r : X) := forall v w, (forall p, R (vec_pos v p) (vec_pos w p)) -> P v <-> mb_is_tuple_in mem r w.
Notation "⟪ A ⟫" := (fun ψ => fol_sem M2 ψ A).
Notation "⟪ A ⟫'" := (fun φ => fol_sem Mn φ A) (at level 1, format "⟪ A ⟫'").
Variable A : fol_form Σn.
Let B := fol_subst (fun v => £ (2+v)) A.
Let d := 0.
Let r := 1.
Definition Σn_Σ2_enc := Σ2_extensional ⟑ Σ2_non_empty d ⟑ Σ2_list_in d (fol_vars B) ⟑ Σn_Σ2 d r B.
End Sign_Sig2_encoding.
Section SAT2_SATn.
Variable n : nat.
Section nested.
Variables (A : fol_form (Σrel n)) (X : Type) (M2 : fo_model (Σrel 2) X) (M2fin : finite_t X) (M2dec : fo_model_dec M2) (ψ : nat -> X) (HA : fol_sem M2 ψ (Σn_Σ2_enc A)).
Let mem a b := fom_rels M2 tt (a##b##ø).
Let mem_dec : forall x y, { mem x y } + { ~ mem x y }.
Proof.
intros x y; apply (@M2dec tt).
Let P x := (if mem_dec x (ψ 0) then true else false) = true.
Let HP0 x : P x <-> mem x (ψ 0).
Proof.
unfold P.
destruct (mem_dec x (ψ 0)); split; try tauto; discriminate.
Let HP1 : finite_t (sig P).
Proof.
apply fin_t_finite_t.
+
intros; apply UIP_dec, bool_dec.
+
apply finite_t_fin_t_dec; auto.
intro; apply bool_dec.
Let Mn : fo_model (Σrel n) (sig P).
Proof.
exists.
+
intros [].
+
intros [] v.
simpl in v.
apply (@mb_is_tuple_in _ mem (ψ 1) n).
apply (vec_map (@proj1_sig _ _) v).
Defined.
Let Mn_dec : fo_model_dec Mn.
Proof.
intros [] v; apply mb_is_tuple_in_dec; auto.
Let R (x : sig P) (y : X) := proj1_sig x = y.
Local Lemma SAT2_to_SATn : exists Y, fo_form_fin_dec_SAT_in A Y.
Proof.
exists (sig P).
destruct HA as (H1 & H2 & H3 & H4).
rewrite Σ2_non_empty_spec in H2.
rewrite Σ2_list_in_spec in H3.
revert H3 H4; set (B := A⦃fun v : nat => in_var (2 + v)⦄); intros H3 H4.
assert (H5 : forall n, In n (fol_vars B) -> P (ψ n)).
{
intros; apply HP0, H3; auto.
}
destruct H2 as (x0 & H0).
generalize H0; intros H2.
apply HP0 in H0.
set (phi := fun n : nat => match in_dec eq_nat_dec n (fol_vars B) with | left H => (exist _ (ψ n) (H5 _ H) : sig P) | right _ => (exist _ x0 H0 : sig P) end).
exists Mn, HP1, Mn_dec, (fun n => phi (2+n)).
unfold B in *; clear B.
rewrite <- Σn_Σ2_correct with (Mn := Mn) (φ := phi) (R := R) in H4.
+
rewrite fol_sem_subst in H4.
revert H4; apply fol_sem_ext; intro; rew fot; auto.
+
intros (x & Hx); exists x; unfold R; simpl; split; auto.
apply HP0 in Hx; auto.
+
intros x Hx; apply HP0 in Hx.
exists (exist _ x Hx); red; simpl; auto.
+
intros v w Hvw.
simpl.
apply fol_equiv_ext; f_equal.
apply vec_pos_ext; intros p.
rewrite vec_pos_map; apply Hvw.
+
intros j Hj; red.
unfold phi.
destruct (in_dec eq_nat_dec j (fol_vars A⦃fun v : nat => in_var (2 + v)⦄)) as [ H | [] ]; auto; simpl.
End nested.
End SAT2_SATn.
Section SATn_SAT2.
Variable n : nat.
Section nested.
Variables (A : fol_form (Σrel n)) (X : Type) (Mn : fo_model (Σrel n) X) (X_fin : finite_t X) (X_discr : discrete X) (Mn_dec : fo_model_dec Mn) (φ : nat -> X) (HA : fol_sem Mn φ A).
Let R := fom_rels Mn tt.
Local Lemma SATn_to_SAT2 : exists Y, fo_form_fin_dec_SAT_in (@Σn_Σ2_enc n A) Y.
Proof.
destruct reln_hfs with (R := fom_rels Mn tt) as (Y & H1 & H2 & mem & H3 & l & r & i & s & H4 & H5 & H6 & H7 & H8 & H9 & H10); auto.
exists Y, (bin_rel_Σ2 mem), H1, (bin_rel_Σ2_dec _ H3), (fun n => match n with | 0 => l | 1 => r | S (S n) => i (φ n) end).
unfold Σn_Σ2_enc; msplit 3; auto.
+
exists (i (φ 0)); simpl; rew fot; simpl; auto.
+
apply Σ2_list_in_spec.
intros n'; simpl.
rewrite fol_vars_map, in_map_iff.
intros (m & <- & ?); auto.
+
rewrite <- Σn_Σ2_correct with (Mn := Mn) (R := fun x y => y = i x) (φ := fun n => match n with 0 => φ 0 | 1 => φ 1 | S (S n) => φ n end); auto.
*
rewrite fol_sem_subst.
revert HA; apply fol_sem_ext.
intros; simpl; rew fot; auto.
*
intros x; exists (i x); split; auto; apply H6.
*
intros v w E; rewrite H9.
apply fol_equiv_ext; f_equal.
apply vec_pos_ext; intro; rew vec.
*
intros n'; rewrite fol_vars_map, in_map_iff.
intros (m & <- & Hm); simpl; auto.
End nested.
End SATn_SAT2.

Let HP0 x : P x <-> mem x (ψ 0).
Proof.
unfold P.
destruct (mem_dec x (ψ 0)); split; try tauto; discriminate.
