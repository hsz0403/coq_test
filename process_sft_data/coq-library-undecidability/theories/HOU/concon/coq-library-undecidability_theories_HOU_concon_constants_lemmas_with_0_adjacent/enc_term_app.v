Require Import List Arith Lia Morphisms Setoid.
From Undecidability.HOU Require Import calculus.calculus.
From Undecidability.HOU Require Import unification.higher_order_unification unification.nth_order_unification concon.conservativity_constants concon.conservativity.
Import ListNotations.
Set Default Proof Using "Type".
Section Retracts.
Variable (X Y: Const).
Variable (RE: retract X Y).
Hypothesis consts_agree: forall x: X, ctype X x = ctype Y (I x).
Let inj (c: X) := const (I c).
Let re (f: Y -> nat) (d: Y) := match tight RE d with | Some x => const x | None => inhab X (f d) (ctype Y d) end.
Program Instance unification_retract {n} (I: orduni n X) : orduni n Y := { s₀ := subst_consts inj s₀; t₀ := subst_consts inj t₀; A₀ := A₀; Gamma₀ := Gamma₀; }.
Next Obligation.
eapply ordertyping_preservation_consts.
eapply H1₀.
intros x H1.
unfold inj.
rewrite consts_agree.
econstructor.
rewrite <-consts_agree.
eapply typing_constants.
eapply H1₀.
eauto.
Next Obligation.
eapply ordertyping_preservation_consts.
eapply H2₀.
intros x H1.
unfold inj.
rewrite consts_agree.
econstructor.
rewrite <-consts_agree.
eapply typing_constants.
eapply H2₀.
eauto.
End Retracts.
Section RemoveConstants.
Variable (X Y: Const) (RE: retract Y X).
Hypothesis (consts_agree: forall y, ctype Y y = ctype X (I y)).
Let R' x := tight RE x.
Let enc_const (A: list X) (x: X): exp Y := match R' x with | Some y => const y | None => match find x A with | Some n => var n | None => var 0 end end.
Let enc_var (A: list X) (y: nat) : exp X := AppR (var (y + length A)) (map var (nats (length A))).
Let enc_term (C: list X) (s: exp X): exp Y := Lambda (length C) (subst_consts (enc_const C) (enc_var C • s)).
Let enc_type (C: list X) (A: type): type := Arr (rev (map (ctype X) C)) A.
Let enc_ctx (C: list X) (Gamma: ctx): ctx := map (enc_type C) Gamma.
Let enc_subst (C: list X) (sigma: fin -> exp X) (x: nat) := enc_term C (sigma x).
Let ι (y: Y) : exp X := const (I y).
Let inv_term C (s: exp Y) := AppR (subst_consts ι s) (map const C).
Let inv_subst C (sigma: fin -> exp Y) (x: nat) := inv_term C (sigma x).
Set Default Proof Using "Type".
Section EncodingLemmas.
Variable (C: list X) (n: nat).
Hypothesis (O: ord' (map (ctype X) C) < n).
Unset Default Proof Using.
Global Instance enc_proper: Proper (equiv (@step X) ++> equiv (@step Y)) (enc_term C).
Proof.
intros ?? H; unfold enc_term; now rewrite H.
Global Instance inv_proper: Proper (equiv (@step Y) ++> equiv (@step X)) (inv_term C).
Proof.
intros ?? H; unfold inv_term; now rewrite H.
Set Default Proof Using "Type".
End EncodingLemmas.
Definition iConsts {n} (I: orduni n X) := filter (fun x => if R' x == None then true else false) (Consts [s₀; t₀]).
Program Instance remove_constants n (I: orduni n X) (H: ord' (map (ctype X) (iConsts I)) < n) : orduni n Y := { s₀ := enc_term (iConsts I) s₀; t₀ := enc_term (iConsts I) t₀; A₀ := enc_type (iConsts I) A₀; Gamma₀ := enc_ctx (iConsts I) Gamma₀; }.
Next Obligation.
eapply remove_constants_ordertyping; eauto using H1₀.
cbn; simplify; intuition.
eapply filter_In; destruct eq_dec; intuition.
Next Obligation.
eapply remove_constants_ordertyping; eauto using H2₀.
cbn; simplify; intuition.
eapply filter_In; destruct eq_dec; intuition.
End RemoveConstants.

Lemma enc_term_app sigma s: (forall x, x ∈ consts s -> R' x = None -> x ∈ C) -> inv_term C (sigma • enc_term C s) >* inv_subst C sigma • s.
Proof using n.
intros H.
unfold enc_term, inv_term.
asimpl.
rewrite subst_consts_Lambda.
rewrite AppR_Lambda'; simplify; eauto.
replace (ι >> _) with ι by (fext; intros ?; reflexivity).
pose (theta x := AppR (subst_consts ι (ren (plus (length C)) (sigma x))) (map var (nats (length C)))).
erewrite subst_consts_subst with (kappa := enc_const C) (theta := theta).
-
rewrite subst_consts_comp.
rewrite subst_consts_subst with (kappa := const) (theta := inv_subst C sigma) .
rewrite subst_consts_ident; eauto.
+
intros x V.
unfold theta, inv_subst.
rewrite subst_consts_AppR, subst_consts_comp.
rewrite map_id_list.
2: intros ??; mapinj; reflexivity.
rewrite subst_consts_ident; eauto.
replace (ι >> _) with (ι >> ren (plus (length C))).
2: fext; intros c; unfold funcomp, enc_const, R'; cbn; now rewrite tight_retr.
rewrite ren_subst_consts_commute.
unfold inv_term.
asimpl.
eapply refl_star.
f_equal.
*
eapply idSubst_exp.
intros y; unfold funcomp.
erewrite sapp_ge_in; simplify; eauto.
*
clear theta V.
eapply list_pointwise_eq.
intros m; rewrite !nth_error_map_option.
destruct (le_lt_dec (length C) m) as [H1|H1].
--
edestruct nth_error_None as [_ ->].
edestruct nth_error_None as [_ ->].
all: cbn; simplify; eauto.
--
rewrite nth_nats; eauto; cbn.
destruct (nth_error_lt_Some _ m C) as [c H3]; eauto.
rewrite H3; cbn.
erewrite nth_error_sapp; eauto.
erewrite map_nth_error; eauto.
+
intros ??.
unfold funcomp.
unfold enc_const.
destruct (R' x) eqn: ?.
cbn.
eapply tight_is_tight in Heqo; now subst.
eapply H in H0; eauto.
eapply find_in in H0 as [m H0]; rewrite H0.
cbn.
erewrite nth_error_sapp; eauto.
erewrite map_nth_error; eauto.
eapply find_Some; eauto.
-
intros; unfold enc_var, theta.
rewrite subst_consts_AppR; cbn.
rewrite AppR_subst; cbn; rewrite it_up_ge; eauto; simplify.
rewrite subst_consts_AppR, subst_consts_comp, subst_consts_ident.
2: intros ?; unfold funcomp, enc_const, R'; cbn; now rewrite tight_retr.
eapply refl_star.
f_equal.
rewrite map_id_list; eauto.
intros ??; mapinj; mapinj; cbn.
rewrite it_up_lt; eauto using nats_lt.
-
intros.
unfold enc_const.
destruct (R' x) eqn: ?.
cbn.
eapply tight_is_tight in Heqo; now subst.
eapply H in H0; eauto.
eapply find_in in H0 as [m H0]; rewrite H0.
eapply find_Some, nth_error_Some_lt in H0.
cbn; erewrite it_up_lt; eauto.
