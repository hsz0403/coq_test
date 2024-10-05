Require Import List Permutation Arith.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec.
From Undecidability.ILL Require Import ILL EILL ill.
Set Implicit Arguments.
Local Infix "~p" := (@Permutation _) (at level 70).
Notation "⦑ c ⦒" := (eill_cmd_map c) (at level 0).
Notation "Σ ; Γ ⊦ u" := (G_eill Σ Γ u) (at level 70, no associativity).
Notation "Γ ⊢ A" := (S_ill_restr Γ A) (at level 70, no associativity).
Section TPS.
Variables (n : nat) (s : ill_vars -> vec nat n -> Prop) (rx : pos n -> ill_vars).
Fact ill_tps_vec_map_list_mono : (forall (p : pos n), s (rx p) (vec_one p)) -> forall v, ill_tps_list s (map £ (vec_map_list v rx)) v.
Proof.
intros H v; rewrite map_vec_map_list.
induction v as [ | p | v w Hv Hw ] using (@vec_nat_induction n).
+
rewrite vec_map_list_zero; simpl; tauto.
+
rewrite vec_map_list_one; simpl.
exists (vec_one p), vec_zero; rew vec; repeat split; auto.
+
apply ill_tps_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
apply ill_tps_app.
exists v, w; repeat split; auto.
Fact ill_tps_vec_map_list : (forall (p : pos n) (v : vec nat n), s (rx p) v <-> v = vec_one p) -> forall v w, ill_tps_list s (map £ (vec_map_list v rx)) w <-> v = w.
Proof.
intros H v; rewrite map_vec_map_list.
induction v as [ | p | v w Hv Hw ] using (@vec_nat_induction n); intros z.
+
rewrite vec_map_list_zero; simpl; tauto.
+
rewrite vec_map_list_one; simpl.
split.
*
intros (a & b & H1 & H2 & H3).
apply H in H2; subst; rew vec.
*
intros [].
exists (vec_one p), vec_zero; rew vec; repeat split; auto.
apply H; auto.
+
split.
*
intros Hz.
apply ill_tps_perm with (1 := vec_map_list_plus _ _ _) in Hz.
apply ill_tps_app in Hz.
destruct Hz as (a & b & H1 & H2 & H3).
apply Hv in H2.
apply Hw in H3.
subst; auto.
*
intros [].
apply ill_tps_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
apply ill_tps_app.
exists v, w; repeat split; auto.
-
apply Hv; auto.
-
apply Hw; auto.
End TPS.
Section g_eill_complete_bound.
Variable (Σ : list eill_cmd) (Γ : list eill_vars) (n : nat).
Notation vars := (flat_map eill_cmd_vars Σ ++ Γ).
Hypothesis (w : vec eill_vars n) (w_surj : forall u, In u vars -> exists p, u = vec_pos w p).
Let rx p := vec_pos w p.
Let Hrx l : incl l (flat_map eill_cmd_vars Σ ++ Γ) -> exists v, l ~p vec_map_list v rx.
Proof.
induction l as [ | x l IHl ]; intros H.
+
exists vec_zero; rewrite vec_map_list_zero; auto.
+
destruct IHl as (v & Hv).
{
intros ? ?; apply H; right; auto.
}
assert (In x vars) as Hx.
{
apply H; left; auto.
}
destruct w_surj with (u := x) as (p & ?); subst; auto.
exists (vec_plus (vec_one p) v).
apply Permutation_sym.
apply Permutation_trans with (1 := vec_map_list_plus _ _ _).
rewrite vec_map_list_one.
apply perm_skip, Permutation_sym; auto.
Let s x v := Σ; vec_map_list v rx ⊦ x.
Notation "⟦ A ⟧" := (ill_tps s A) (at level 65).
Notation "'[<' Γ '|-' A '>]'" := (ill_sequent_tps s Γ A) (at level 65).
End g_eill_complete_bound.
Section g_eill_complete.
Variable (Σ : list eill_cmd) (Γ : list eill_vars).
Notation vars := (flat_map eill_cmd_vars Σ ++ Γ).
Let vv := nat_sort vars.
Let Hvv1 : list_injective vv.
Proof.
apply nat_sorted_injective, nat_sort_sorted.
Let Hvv2 : incl vv (flat_map eill_cmd_vars Σ ++ Γ) /\ incl (flat_map eill_cmd_vars Σ ++ Γ) vv.
Proof.
apply nat_sort_eq.
Let n := length vv.
Let w : vec eill_vars n := proj1_sig (list_vec_full vv).
Let Hw : vec_list w = vv.
Proof.
apply (proj2_sig (list_vec_full vv)).
Let w_surj : forall u, In u vars -> exists p, u = vec_pos w p.
Proof.
intros u Hu.
apply Hvv2 in Hu; rewrite <- Hw in Hu.
revert Hu; apply vec_list_inv.
Variables (x : eill_vars) (Hvalid : forall n s, @ill_sequent_tps n s (map (fun c => !⦑c⦒) Σ ++ map £ Γ) (£ x) vec_zero).
End g_eill_complete.
From Undecidability.ILL Require Import CLL ill_cll schellinx.
Fact eill_no_bot c : ~ ill_has_bot ⦑ c ⦒.
Proof.
induction c; simpl; tauto.
Section correctness_results_for_the_reduction.
Variables (Σ : list eill_cmd) (Γ : list eill_vars) (u : nat).
Notation Σi := (map (fun c => ill_ban ⦑c⦒) Σ).
Notation Γi := (map ill_var Γ).
Notation ui := (ill_var u).
Notation Σc := (map (fun c => cll_una cll_bang [⦑c⦒]) Σ).
Notation Γc := (map cll_var Γ).
Notation uc := (cll_var u).
Tactic Notation "solve" "with" int(i) int(j) := let H := fresh in split; [ intro; now do i apply G_eill_correct | intros H; now do j apply G_eill_correct in H ].
Let not_bot f : In f (ui :: Σi ++ Γi) -> ~ ill_has_bot f.
Proof.
simpl; rewrite in_app_iff, !in_map_iff.
intros [ <- | [ (? & <- & ?) | (? & <- & ?) ] ]; simpl; auto; apply eill_no_bot.
End correctness_results_for_the_reduction.

Let Hvv1 : list_injective vv.
Proof.
apply nat_sorted_injective, nat_sort_sorted.
