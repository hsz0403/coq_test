Require Import List Arith Lia Relations.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_congruence fo_sat.
Set Implicit Arguments.
Section remove_interpreted_symbol.
Variables (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ)) (e : rels Σ) (H_ae : ar_rels _ e = 2) (He : In e lr).
Notation 𝕋 := (fol_term Σ).
Notation 𝔽 := (fol_form Σ).
Notation "x ≡ y" := (@fol_atom Σ e (cast (x##y##ø) (eq_sym H_ae))) (at level 59).
Definition Σ_noeq A := fol_congruence H_ae ls lr ⟑ A.
Section soundness.
Variable (A : 𝔽) (X : Type).
End soundness.
Section completeness.
Hint Resolve finite_t_pos : core.
Variable (A : 𝔽) (HA1 : incl (fol_syms A) ls) (HA2 : incl (fol_rels A) lr).
End completeness.
End remove_interpreted_symbol.

Theorem Σ_noeq_sound : fo_form_fin_dec_eq_SAT_in _ H_ae A X -> fo_form_fin_dec_SAT_in (Σ_noeq A) X.
Proof.
intros (M & H1 & H2 & HE & phi & H5).
exists M, H1, H2, phi; unfold Σ_noeq.
rewrite fol_sem_bin_fix; split; auto.
rewrite fol_sem_congruence.
split; [ | msplit 2 ].
+
split.
*
intros s _ v w H; rewrite HE.
f_equal; apply vec_pos_ext; intros p.
apply HE, H.
*
intros r _ v w H.
apply fol_equiv_ext; f_equal.
apply vec_pos_ext; intros p.
apply HE, H.
+
intros ?; rewrite HE; auto.
+
intros ? ? ?; rewrite !HE; intros; subst; auto.
+
intros ? ?; rewrite !HE; intros; subst; auto.
