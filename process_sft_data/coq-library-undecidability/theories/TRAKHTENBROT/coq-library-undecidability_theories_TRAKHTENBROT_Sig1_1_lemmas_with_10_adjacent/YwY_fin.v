Require Import List Arith Bool Lia Eqdep_dec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat Sig_no_syms.
Set Implicit Arguments.
Fixpoint find_non_empty_word X (l : list (list X)) : { s & { w | In (s::w) l } } + { concat l = nil }.
Proof.
destruct l as [ | [ | s w ] l ].
+
right; auto.
+
destruct (find_non_empty_word X l) as [ (s & w & H) | H ].
*
left; exists s, w; right; auto.
*
right; simpl; auto.
+
left; exists s, w; left; auto.
Local Notation ø := vec_nil.
Section fot_word_var.
Variable (X : Type).
Implicit Type t : fo_term (fun _ : X => 1).
Fixpoint fot_var t := match t with | in_var i => i | in_fot s v => fot_var (vec_pos v pos0) end.
Fixpoint fot_word t := match t with | in_var i => nil | in_fot s v => s::fot_word (vec_pos v pos0) end.
Fixpoint fot_word_var w i : fo_term (fun _ : X => 1) := match w with | nil => in_var i | s::w => in_fot s (fot_word_var w i##ø) end.
Fact fot_word_var_eq t : t = fot_word_var (fot_word t) (fot_var t).
Proof.
induction t as [ | s v IH ]; simpl in *; auto; f_equal.
generalize (IH pos0); clear IH; vec split v with t; vec nil v; clear v; simpl.
intro; f_equal; auto.
Fact fot_word_eq w i : fot_word (fot_word_var w i) = w.
Proof.
induction w; simpl; f_equal; auto.
Fact fot_var_eq w i : fot_var (fot_word_var w i) = i.
Proof.
induction w; simpl; f_equal; auto.
End fot_word_var.
Section Σ11_words.
Variable (X Y : Type).
Definition Σ11 : fo_signature.
Proof.
exists X Y; intros _.
+
exact 1.
+
exact 1.
Defined.
Fixpoint Σ11_words (A : fol_form Σ11) : list (list X) := match A with | ⊥ => nil | fol_atom r v => (fot_word (vec_pos v pos0))::nil | fol_bin _ A B => Σ11_words A++Σ11_words B | fol_quant _ A => Σ11_words A end.
End Σ11_words.
Section Σfull_mon_rem.
Variable (Y : Type) (HY : finite_t Y) (n m : nat).
Notation X := (pos n).
Let Yw := { w : list X | length w < S m }.
Let YwY_fin : finite_t (Yw*Y).
Proof.
apply finite_t_prod; auto.
apply finite_t_list, finite_t_pos.
Let lwY := proj1_sig YwY_fin.
Let HlwY p : In p lwY.
Proof.
apply (proj2_sig YwY_fin).
Notation Σ := (Σ11 X Y).
Notation Σ' := (Σ11 X (list X*Y + Y)).
Fixpoint Σfull_mon_rec (A : fol_form Σ) : fol_form Σ' := match A with | ⊥ => ⊥ | fol_atom r v => let w := fot_word (vec_head v) in let i := fot_var (vec_head v) in @fol_atom Σ' (inl (rev w,r)) (£i##ø) | fol_bin b A B => fol_bin b (Σfull_mon_rec A) (Σfull_mon_rec B) | fol_quant q A => fol_quant q (Σfull_mon_rec A) end.
Fact Σfull_mon_rec_syms A : fol_syms (Σfull_mon_rec A) = nil.
Proof.
induction A as [ | r v | b A HA B HB | q A HA ].
1,2,4: simpl; tauto.
simpl; rewrite HA, HB; auto.
Variable (A : fol_form Σ) (HwA : forall w, In w (Σ11_words A) -> length w < S m).
Let Eq (p : Yw * Y) := let (w,r) := p in let (w,_) := w in match w with | nil => @fol_atom Σ' (inl (nil,r)) (£0##ø) ↔ @fol_atom Σ' (inr r) (£0##ø) | s::w' => @fol_atom Σ' (inl (w',r)) (@in_fot _ (ar_syms Σ') s (£0##ø)##ø) ↔ @fol_atom Σ' (inl (w,r)) (£0##ø) end.
Let Eq' (p : Yw * Y) := let (w,r) := p in let (w,_) := w in match w with | nil => @fol_atom Σ' (inl (nil,r)) (£n##ø) ↔ @fol_atom Σ' (inr r) (£n##ø) | s::w' => @fol_atom Σ' (inl (w',r)) (£(pos2nat s)##ø) ↔ @fol_atom Σ' (inl (w,r)) (£n##ø) end.
Definition Σfull_mon_red : fol_form Σ' := Σfull_mon_rec A ⟑ ∀ fol_lconj (map Eq lwY).
Variable (K : Type).
Let Fixpoint f (M : fo_model Σ K) w x := match w with | nil => x | s::w => f M w (fom_syms M s (x##ø)) end.
Let f_app M w1 w2 x : f M (w1++w2) x = f M w2 (f M w1 x).
Proof.
revert x; induction w1; simpl; auto.
Let f_snoc M w s x : f M (w++s::nil) x = fom_syms M s (f M w x##ø).
Proof.
rewrite f_app; auto.
Section soundness.
Variable (M : fo_model Σ K).
Let M' : fo_model Σ' K.
Proof.
split.
+
exact (fom_syms M).
+
intros [ (w,r) | r ]; simpl in r |- *.
*
exact (fun v => fom_rels M r (f M w (vec_head v)##ø)).
*
exact (fom_rels M r).
Defined.
Fact Σfull_mon_rec_sound φ : fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
Proof.
revert φ HwA; induction A as [ | r v | b B HB C HC | q B HB ]; intros φ HA.
+
simpl; tauto.
+
simpl in v; unfold Σfull_mon_rec.
revert HA; vec split v with t; vec nil v; clear v; simpl vec_head; simpl syms; intros HA.
specialize (HA _ (or_introl eq_refl)); simpl in HA |- *.
replace (fo_term_sem M φ t) with (fo_term_sem M φ (fot_word_var (fot_word t) (fot_var t))).
*
simpl; apply fol_equiv_ext; do 2 f_equal.
generalize (fot_word t) (fot_var t); clear t HA; intros w.
induction w as [ | s w IHw ]; simpl; auto; intros i.
rewrite f_snoc; simpl; do 2 f_equal; auto.
*
f_equal; symmetry; apply fot_word_var_eq.
+
simpl; apply fol_bin_sem_ext.
*
apply HB; intros ? ?; apply HA, in_app_iff; auto.
*
apply HC; intros ? ?; apply HA, in_app_iff; auto.
+
simpl; apply fol_quant_sem_ext; intro; apply HB; auto.
Variable (Kfin : finite_t K) (Mdec : fo_model_dec M) (φ : nat -> K) (HA : fol_sem M φ A).
End soundness.
Section completeness.
Variable (M' : fo_model Σ' K).
Let M : fo_model Σ K.
Proof.
split.
+
exact (fom_syms M').
+
exact (fun r => fom_rels M' (inr r)).
Defined.
Section Σfull_mon_rec_complete.
Hypothesis HM1' : forall s w r x, length (s::w) < S m -> fom_rels M' (inl (s::w, r)) (x##ø) <-> fom_rels M' (inl (w, r)) (fom_syms M s (x##ø)##ø).
Hypothesis HM2' : forall r x, fom_rels M' (inr r) (x##ø) <-> fom_rels M' (inl (nil,r)) (x##ø).
Let Hf φ w i : f M (rev w) (φ i) = fo_term_sem M φ (fot_word_var w i).
Proof.
induction w; simpl; auto.
rewrite f_snoc; simpl in *; rewrite IHw; auto.
Fact Σfull_mon_rec_complete φ : fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
Proof.
revert φ HwA; induction A as [ | r v | b B HB C HC | q B HB ]; intros φ HwA.
+
simpl; tauto.
+
simpl in v; unfold Σfull_mon_rec.
revert HwA; vec split v with t; vec nil v; clear v; simpl vec_head; simpl syms; intros HwA.
specialize (HwA _ (or_introl eq_refl)); simpl in HwA |- *.
replace (fo_term_sem M φ t) with (fo_term_sem M φ (fot_word_var (fot_word t) (fot_var t))).
*
revert HwA; generalize (fot_word t) (fot_var t); intros w i.
rewrite <- (rev_length w), <- Hf.
simpl; generalize (rev w) (φ i); clear w; intros w.
induction w as [ | s w IHw ]; simpl; auto; intros Hw x.
-
rewrite HM2'; tauto.
-
rewrite HM1', IHw; simpl; try tauto; lia.
*
f_equal; symmetry; apply fot_word_var_eq.
+
apply fol_bin_sem_ext.
*
apply HB; intros ? ?; apply HwA, in_app_iff; auto.
*
apply HC; intros ? ?; apply HwA, in_app_iff; auto.
+
simpl; apply fol_quant_sem_ext; intro; apply HB; auto.
End Σfull_mon_rec_complete.
Variable (Kfin : finite_t K) (M'dec : fo_model_dec M') (φ : nat -> K) (HA : fol_sem M' φ Σfull_mon_red).
End completeness.
Definition Σfull_mon_red' : fol_form Σ' := Σfull_mon_rec A ⟑ ∀ fol_mquant fol_ex n (fol_lconj (map Eq' lwY)).
Local Lemma Σfull_mon_red'_sound : fo_form_fin_dec_SAT_in Σfull_mon_red K -> fo_form_fin_dec_SAT_in Σfull_mon_red' K.
Proof.
intros (M & Kfin & Mdec & φ & H1 & H2); simpl in H1, H2.
exists M, Kfin, Mdec, φ; simpl; split; auto.
intros x; specialize (H2 x).
rewrite fol_sem_mexists.
exists (vec_set_pos (fun p => fom_syms M p (x##ø))).
rewrite fol_sem_lconj; intros g; rewrite in_map_iff.
intros (c & <- & Hg).
rewrite fol_sem_lconj in H2.
specialize (H2 (Eq c) (in_map _ _ _ Hg)).
clear Hg; revert H2.
destruct c as (([ | s w ],?),r); simpl.
+
rewrite env_vlift_fix1 with (k := 0); simpl; auto.
+
rewrite env_vlift_fix1 with (k := 0).
rewrite env_vlift_fix0; simpl; rew vec.
Section Σfull_mon_red'_complete.
Variable (M : fo_model Σ' K) (Kfin : finite_t K) (Mdec : fo_model_dec M) (φ : nat -> K) (HA : fol_sem M φ Σfull_mon_red').
Let R x (v : vec _ n) := fol_sem M (env_vlift x·φ v) (fol_lconj (map Eq' lwY)).
Let Rreif : { f : K -> vec K n | forall x, R x (f x) }.
Proof.
apply finite_t_dec_choice.
+
apply finite_t_vec; auto.
+
intros x v; apply fol_sem_dec; auto.
+
simpl in HA; apply proj2 in HA.
intros x; generalize (HA x).
rewrite fol_sem_mexists; auto.
Let g := proj1_sig Rreif.
Let Hg x : fol_sem M (env_vlift x·φ (g x)) (fol_lconj (map Eq' lwY)).
Proof.
apply (proj2_sig Rreif).
Let M' : fo_model Σ' K.
Proof.
split.
+
simpl; intros p v.
exact (vec_pos (g (vec_head v)) p).
+
exact (fom_rels M).
Defined.
Local Lemma Σfull_mon_red'_complete : fo_form_fin_dec_SAT_in Σfull_mon_red K.
Proof.
exists M', Kfin, Mdec, φ.
simpl; split.
+
simpl in HA; generalize (proj1 HA).
apply fo_model_nosyms.
*
apply Σfull_mon_rec_syms.
*
intros; simpl; tauto.
+
intros x.
specialize (Hg x).
rewrite fol_sem_lconj in Hg.
rewrite fol_sem_lconj.
intros u; rewrite in_map_iff.
intros (c & <- & Hc).
specialize (Hg (Eq' c) (in_map _ _ _ Hc)).
revert Hg.
destruct c as (([|s w]&?),r); simpl.
*
rewrite env_vlift_fix1 with (k := 0); simpl; auto.
*
rewrite env_vlift_fix1 with (k := 0).
rewrite env_vlift_fix0; simpl; rew vec.
End Σfull_mon_red'_complete.
End Σfull_mon_rem.
Section Σ11_reduction.
Variable (n : nat) (Y : Type) (HY : finite_t Y) (A : fol_form (Σ11 (pos n) Y)) (K : Type).
Let m := lmax (map (@length _) (Σ11_words A)).
Let Hm w : In w (Σ11_words A) -> length w < S m.
Proof.
intros Hw; apply le_n_S, lmax_prop, in_map_iff.
exists w; auto.
Definition Σ11_red := Σfull_mon_red' HY m A.
End Σ11_reduction.
Section Σ11_Σ1.
Variable (n : nat) (Y : Type) (HY : finite_t Y) (A : fol_form (Σ11 (pos n) Y)).
End Σ11_Σ1.

Fixpoint find_non_empty_word X (l : list (list X)) : { s & { w | In (s::w) l } } + { concat l = nil }.
Proof.
destruct l as [ | [ | s w ] l ].
+
right; auto.
+
destruct (find_non_empty_word X l) as [ (s & w & H) | H ].
*
left; exists s, w; right; auto.
*
right; simpl; auto.
+
Admitted.

Fact fot_word_var_eq t : t = fot_word_var (fot_word t) (fot_var t).
Proof.
induction t as [ | s v IH ]; simpl in *; auto; f_equal.
generalize (IH pos0); clear IH; vec split v with t; vec nil v; clear v; simpl.
Admitted.

Fact fot_word_eq w i : fot_word (fot_word_var w i) = w.
Proof.
Admitted.

Fact fot_var_eq w i : fot_var (fot_word_var w i) = i.
Proof.
Admitted.

Definition Σ11 : fo_signature.
Proof.
exists X Y; intros _.
+
exact 1.
+
Admitted.

Let HlwY p : In p lwY.
Proof.
Admitted.

Fact Σfull_mon_rec_syms A : fol_syms (Σfull_mon_rec A) = nil.
Proof.
induction A as [ | r v | b A HA B HB | q A HA ].
1,2,4: simpl; tauto.
Admitted.

Let f_app M w1 w2 x : f M (w1++w2) x = f M w2 (f M w1 x).
Proof.
Admitted.

Let f_snoc M w s x : f M (w++s::nil) x = fom_syms M s (f M w x##ø).
Proof.
Admitted.

Let M' : fo_model Σ' K.
Proof.
split.
+
exact (fom_syms M).
+
intros [ (w,r) | r ]; simpl in r |- *.
*
exact (fun v => fom_rels M r (f M w (vec_head v)##ø)).
*
Admitted.

Fact Σfull_mon_rec_sound φ : fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
Proof.
revert φ HwA; induction A as [ | r v | b B HB C HC | q B HB ]; intros φ HA.
+
simpl; tauto.
+
simpl in v; unfold Σfull_mon_rec.
revert HA; vec split v with t; vec nil v; clear v; simpl vec_head; simpl syms; intros HA.
specialize (HA _ (or_introl eq_refl)); simpl in HA |- *.
replace (fo_term_sem M φ t) with (fo_term_sem M φ (fot_word_var (fot_word t) (fot_var t))).
*
simpl; apply fol_equiv_ext; do 2 f_equal.
generalize (fot_word t) (fot_var t); clear t HA; intros w.
induction w as [ | s w IHw ]; simpl; auto; intros i.
rewrite f_snoc; simpl; do 2 f_equal; auto.
*
f_equal; symmetry; apply fot_word_var_eq.
+
simpl; apply fol_bin_sem_ext.
*
apply HB; intros ? ?; apply HA, in_app_iff; auto.
*
apply HC; intros ? ?; apply HA, in_app_iff; auto.
+
Admitted.

Theorem Σfull_mon_rem_sound : fo_form_fin_dec_SAT_in Σfull_mon_red K.
Proof.
exists M', Kfin.
exists.
{
intros [ (w,r) | r ]; simpl in r |- *; intro; apply Mdec.
}
exists φ; simpl; split.
+
apply Σfull_mon_rec_sound; auto.
+
intro x; rewrite fol_sem_lconj.
intros ?; rewrite in_map_iff.
intros ((([|s w]&Hw),r) & <- & Hr); unfold Eq.
*
simpl; auto.
*
Admitted.

Let M : fo_model Σ K.
Proof.
split.
+
exact (fom_syms M').
+
Admitted.

Let Hf φ w i : f M (rev w) (φ i) = fo_term_sem M φ (fot_word_var w i).
Proof.
induction w; simpl; auto.
Admitted.

Fact Σfull_mon_rec_complete φ : fol_sem M' φ (Σfull_mon_rec A) <-> fol_sem M φ A.
Proof.
revert φ HwA; induction A as [ | r v | b B HB C HC | q B HB ]; intros φ HwA.
+
simpl; tauto.
+
simpl in v; unfold Σfull_mon_rec.
revert HwA; vec split v with t; vec nil v; clear v; simpl vec_head; simpl syms; intros HwA.
specialize (HwA _ (or_introl eq_refl)); simpl in HwA |- *.
replace (fo_term_sem M φ t) with (fo_term_sem M φ (fot_word_var (fot_word t) (fot_var t))).
*
revert HwA; generalize (fot_word t) (fot_var t); intros w i.
rewrite <- (rev_length w), <- Hf.
simpl; generalize (rev w) (φ i); clear w; intros w.
induction w as [ | s w IHw ]; simpl; auto; intros Hw x.
-
rewrite HM2'; tauto.
-
rewrite HM1', IHw; simpl; try tauto; lia.
*
f_equal; symmetry; apply fot_word_var_eq.
+
apply fol_bin_sem_ext.
*
apply HB; intros ? ?; apply HwA, in_app_iff; auto.
*
apply HC; intros ? ?; apply HwA, in_app_iff; auto.
+
Admitted.

Let YwY_fin : finite_t (Yw*Y).
Proof.
apply finite_t_prod; auto.
apply finite_t_list, finite_t_pos.
