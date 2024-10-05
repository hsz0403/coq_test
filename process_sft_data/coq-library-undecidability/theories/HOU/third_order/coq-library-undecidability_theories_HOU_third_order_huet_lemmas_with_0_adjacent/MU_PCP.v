Set Implicit Arguments.
Require Import RelationClasses Morphisms List Arith Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus unification.unification.
From Undecidability.HOU Require Import third_order.pcp third_order.encoding.
Import ListNotations.
Set Default Proof Using "Type".
Section HuetReduction.
Variable (X: Const).
Let v n: fin := n.
Let u n: fin := (S n).
Let h: exp X := var 0.
Let f: exp X := var 3.
Let g: exp X := var 4.
Instance PCP_to_U (S: list card) : orduni 3 X.
Proof with cbn [ord' ord alpha]; simplify; cbn; (eauto 2).
refine {| Gamma₀ := [Arr (repeat (alpha → alpha) (length S)) alpha; (alpha → alpha) → alpha]; s₀ := lambda lambda lambda h (AppR f (Enc 1 2 (heads S))) (AppR f (repeat (var (u 1)) (length S))); t₀ := lambda lambda lambda h (AppR f (Enc 1 2 (tails S))) (var (u 1) (g (var (u 1)))); A₀ := (alpha → alpha) → (alpha → alpha) → (alpha → alpha → alpha) → alpha; H1₀ := HGamma₀s₀A₀ S; H2₀ := HGamma₀t₀A₀ S; |}.
Defined.
Section ForwardDirection.
Definition ginst (I: list nat) : exp X := lambda AppL (repeat (var 0) (pred (|I|))) (var 1).
End ForwardDirection.
Section BackwardDirection.
Variables (s t: exp X) (x: nat) (sigma: fin -> exp X) (S: list (exp X)).
Hypothesis (H1: forall y, isVar (sigma y) /\ sigma y <> var x).
Hypothesis (N: normal s).
Hypothesis (EQ: S .+ sigma • s ≡ (var x) t).
End BackwardDirection.
End HuetReduction.

Lemma MU_PCP S': NOU 3 (PCP_to_U S') -> PCP S'.
Proof.
intros (Delta & sigma & T & H & N); cbn in *.
repeat apply equiv_lam_elim in H.
eapply equiv_app_elim in H as [EQ2 EQ1]; cbn; intuition.
eapply equiv_app_elim in EQ2 as [_ EQ2]; cbn; intuition.
rewrite !AppR_subst in EQ1; rewrite !AppR_subst in EQ2.
rewrite !Enc_subst_id in EQ2;try reflexivity.
cbn in *.
unfold funcomp in *.
rewrite !ren_plus_base, !ren_plus_combine in *; change (1 + 1 + 1) with 3 in *.
unfold shift, var_zero in *.
rewrite map_id_list in EQ1; [| intros ? ? % repeated_in; now subst ].
assert (Delta ⊢(3) sigma 0 : Arr (repeat (alpha → alpha) (length S')) alpha) as T1 by now apply T.
specialize (N 0) as N2; eapply normal_nf in N2 as N3.
destruct N3 as [k x t' T' Hi H ->].
eapply Lambda_ordertyping_inv in T1 as (L & B & H0 & H1 & <-).
eapply id in H0 as T2.
assert (|L | <= |S'|) as L1 by (eapply (f_equal arity) in H1; simplify in H1; rewrite H1; eauto).
symmetry in H1; eapply Arr_inversion in H1 as (L2 & H1 & H2); simplify; try lia.
eapply repeated_app_inv in H1 as (H1 & H3 & H4); (eauto 2).
rewrite H4 in H2; subst B.
rewrite H3 in *; simplify in *.
clear H3 H4 L1.
revert H0 H1 EQ1 EQ2 T2 N2.
generalize (length L); generalize (length L2); clear L L2.
intros l k H0 H1 EQ1 EQ2 T2 N2.
edestruct (@list_decompose_alt k _ S') as (S1 & S2 & H4 & H5); try lia; subst S'.
rewrite !Lambda_ren in EQ1; rewrite !Lambda_ren in EQ2.
simplify in EQ1 EQ2; rewrite !AppR_app in EQ1; rewrite !AppR_app in EQ2.
simplify in H1; assert (length S1 = l) as H2 by lia; clear H1; subst.
rewrite !AppR_Lambda' in EQ1, EQ2; simplify; (eauto 2).
rewrite AppR_Lambda' in EQ2; simplify; (eauto 2).
rewrite it_up_var_sapp in EQ1; simplify; intros; try lia.
rewrite !it_up_var_sapp in EQ2; simplify; intros; try lia.
destruct (AppL_decomposition (AppR x T') (|S2|)) as [[I t] (H1&H2&H3)].
rewrite H2 in EQ1, EQ2.
destruct S1.
+
rewrite H2 in *.
assert (normal t) by now eapply normal_AppL_right, normal_Lambda.
rewrite !AppL_subst in EQ1; rewrite !AppL_subst in EQ2.
cbn -[add] in *.
rewrite !select_variables_subst in EQ2.
rewrite !select_variables_subst in EQ1.
all: simplify; (eauto 2).
rewrite <-!select_map, !enc_concat in EQ2.
eapply AppL_ordertyping_inv in T2 as (L' & B & H8 & H9).
eapply enc_eq in EQ2; (eauto 2).
2 - 3: split; intros EQ3; eapply end_is_var_typed in EQ3 as (? & ? & ? & ?); cbn; simplify.
6, 9, 15, 21 :now eauto.
3, 8, 13, 16 : now eauto.
2, 6, 10, 13: eapply H3; cbn; (eauto 1); cbn; now simplify in *.
3, 5, 8, 11: eauto.
3, 5, 9: eauto.
3, 4, 6:eauto.
2 - 3: intros; cbn; unfold funcomp, u, v; intuition discriminate.
exists I; intuition; eauto using nats_lt; (eauto 2).
2: rewrite <-!select_map; (eauto 2).
subst; cbn [map select concat AppL] in H6, EQ1.
eapply end_is_var in EQ1 as (? & ? & ? & ?); eauto; simplify.
eapply H3; cbn; (eauto 1); cbn; now simplify in *.
intros; cbn; intuition; discriminate.
intros ? ? % repeated_in; subst; (eauto 2).
+
eapply id in T2 as T3.
eapply AppR_ordertyping_inv in T2 as (L' & T2 & T4).
destruct x as [i | | |]; cbn in H; (eauto 2).
*
inv T4.
assert (i < length S2 \/ i >= length S2) as [H42|H42] by lia.
**
rewrite nth_error_app1, nth_error_repeated in H6; simplify; (eauto 2).
injection H6 as H6.
eapply (f_equal ord) in H6.
simplify in H6.
symmetry in H6; eapply Nat.eq_le_incl in H6; simplify in H6.
intuition.
cbn in H6.
lia.
**
rewrite <-H2 in EQ1.
asimpl in EQ1.
rewrite sapp_ge_in in EQ1; simplify; (eauto 2).
eapply equiv_head_equal in EQ1; simplify; cbn; (eauto 2).
simplify in EQ1; cbn in EQ1.
discriminate EQ1.
*
rewrite <-H2 in EQ1.
exfalso.
asimpl in EQ1.
eapply equiv_head_equal in EQ1; cbn; simplify; cbn; intuition.
cbn in EQ1; simplify in EQ1; discriminate.
