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

Lemma enc_subst_term_reduce tau s: (forall x c, c ∈ consts (tau x) -> R' c = None -> c ∈ C) -> (forall x, x ∈ consts s -> R' x = None -> x ∈ C) -> enc_subst C tau • enc_term C s >* enc_term C (tau • s).
Proof using n.
intros H1 H2; unfold enc_term.
asimpl.
eapply Lambda_steps_proper.
rewrite subst_consts_subst; eauto.
-
intros x ?.
unfold funcomp at 1.
unfold enc_var.
rewrite !subst_consts_AppR, AppR_subst; cbn.
rewrite it_up_ge; simplify; eauto.
rewrite map_id_list; cbn.
rewrite map_map; cbn.
change (fun x => @var Y x) with (@var Y).
unfold enc_subst at 1, enc_term.
rewrite Lambda_ren.
rewrite AppR_Lambda'; simplify; eauto.
asimpl.
rewrite subst_consts_subst; eauto.
+
intros ? ?; unfold funcomp.
unfold enc_var.
rewrite idSubst_exp; eauto.
intros y; cbn.
destruct (le_lt_dec (length C) y).
rewrite it_up_ren_ge, le_plus_minus_r, sapp_ge_in; simplify; eauto.
erewrite it_up_ren_lt, nth_error_sapp; eauto.
erewrite map_nth_error; eauto using nth_nats.
+
unfold enc_const; intros c; destruct (R' c) eqn: ?; cbn; eauto.
intros [m H'] % H1 % find_in; eauto; rewrite H'.
eapply find_Some, nth_error_Some_lt in H'.
cbn; unfold funcomp; erewrite it_up_ren_lt, nth_error_sapp; eauto.
erewrite map_nth_error; eauto using nth_nats.
+
intros ? ?; mapinj; mapinj; cbn; rewrite it_up_lt; eauto using nats_lt.
-
unfold enc_const; intros c; destruct (R' c) eqn: ?; cbn; eauto.
intros [m H'] % H2 % find_in; eauto; rewrite H'.
eapply find_Some, nth_error_Some_lt in H'.
cbn; erewrite it_up_lt; eauto.
