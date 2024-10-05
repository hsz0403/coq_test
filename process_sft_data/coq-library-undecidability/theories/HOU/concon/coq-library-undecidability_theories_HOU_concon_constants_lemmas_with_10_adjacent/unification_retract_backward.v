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

Lemma inj_ren delta: inj >> ren delta = inj.
Proof.
Admitted.

Lemma re_ren f delta: re f >> ren delta = re (f >> delta).
Proof.
fext; intros x; unfold funcomp, re.
destruct tight; eauto.
Admitted.

Lemma subst_consts_inject_forward sigma s: subst_consts inj (sigma • s) = (sigma >> subst_consts inj) • (subst_consts inj s).
Proof.
induction s in sigma |-*; cbn in *; intuition.
-
f_equal.
rewrite inj_ren.
rewrite IHs.
f_equal.
fext; intros []; cbn; eauto.
rewrite <-inj_ren with (delta := shift) at 1.
unfold funcomp at 2.
now rewrite ren_subst_consts_commute.
-
Admitted.

Lemma subst_consts_inject_backwards sigma s f: subst_consts (re f) (sigma • subst_consts inj s) = (sigma >> subst_consts (re f)) • s.
Proof.
induction s in sigma, f |-*; cbn.
-
reflexivity.
-
unfold funcomp.
unfold re.
unfold tight.
rewrite retr.
destruct (I c == I c); intuition.
-
f_equal.
rewrite subst_consts_up, inj_ren, re_ren; eauto.
-
Admitted.

Lemma inj_typing n sigma Gamma Delta: Delta ⊩(n) sigma : Gamma -> Delta ⊩(n) sigma >> subst_consts inj : Gamma.
Proof using consts_agree.
intros ????.
eapply ordertyping_preservation_consts; eauto.
intros ??; unfold inj.
rewrite consts_agree.
econstructor; rewrite <-consts_agree.
Admitted.

Lemma re_typing n Delta f sigma Gamma: 1 <= n -> Delta ⊩(n) sigma : Gamma -> (forall x c, x ∈ dom Gamma -> c ∈ consts (sigma x) -> nth Delta (f c) = Some (target (ctype Y c))) -> Delta ⊩(n) sigma >> subst_consts (re f) : Gamma.
Proof using consts_agree.
intros L T Sub x A H; unfold funcomp.
eapply ordertyping_preservation_consts; eauto.
intros y H'.
unfold re.
destruct (tight RE y) eqn: EQr.
-
eapply tight_is_tight in EQr.
subst.
rewrite <-consts_agree.
econstructor.
rewrite consts_agree.
eapply typing_constants; eauto.
-
Admitted.

Lemma unification_retract_forward n (I: orduni n X): OU n X I -> OU n Y (unification_retract I).
Proof.
intros (Delta & sigma & T & EQ).
exists Delta.
exists (sigma >> subst_consts inj).
split.
-
now eapply inj_typing.
-
unfold s₀, t₀; cbn.
rewrite <-!subst_consts_inject_forward.
Admitted.

Lemma unification_constants_monotone n: 1 <= n -> OU n X ⪯ OU n Y.
Proof using re inj consts_agree RE.
intros H; exists unification_retract.
Admitted.

Lemma remove_constants_ordertyping Gamma s A: Gamma ⊢(n) s : A -> (forall x, x ∈ consts s -> R' x = None -> x ∈ C) -> enc_ctx C Gamma ⊢(n) enc_term C s : enc_type C A.
Proof using consts_agree O.
intros T H.
eapply Lambda_ordertyping; simplify; eauto.
eapply ordertyping_preservation_consts.
eapply ordertyping_weak_preservation_under_substitution; eauto.
-
intros y B H1 H2.
unfold enc_var.
eapply AppR_ordertyping.
+
eapply map_var_typing with (L := map (ctype X) C).
*
intros x; rewrite dom_lt_iff; simplify.
intros ? % nats_lt; lia.
*
rewrite select_nats.
rewrite firstn_app; simplify.
rewrite <-firstn_all; cbn; now simplify.
*
eauto.
+
econstructor; simplify; intuition.
eapply vars_ordertyping_nth with (n0 := n) (Gamma0 := Gamma) in H1; eauto.
unfold enc_ctx; erewrite nth_error_app2, map_nth_error; simplify; now eauto.
-
intros x H'.
unfold enc_const.
eapply consts_subst_in in H' as [].
destruct (R' x) eqn: EQ.
+
eapply tight_is_tight in EQ as EQ'; subst x.
rewrite <-consts_agree.
econstructor.
rewrite consts_agree.
eapply typing_constants; eauto.
+
destruct find eqn: H1.
*
eapply find_Some in H1.
econstructor.
rewrite <-O.
now eapply ord'_in, in_map, H.
rewrite nth_error_app1; simplify; eauto using nth_error_Some_lt.
erewrite map_nth_error; now eauto.
*
exfalso.
eapply find_not_in in H1; intuition.
+
unfold enc_var in H0.
destruct H0.
intuition.
rewrite consts_AppR in H2.
simplify in H2.
unfold Consts in H2; eapply in_flat_map in H2 as [].
intuition.
mapinj.
Admitted.

Lemma inv_term_typing Gamma s A: Gamma ⊢(n) s : enc_type C A -> Gamma ⊢(n) inv_term C s : A.
Proof using consts_agree O.
intros H; unfold inv_term.
eapply AppR_ordertyping with (L := map (ctype X) C).
eapply const_ordertyping_list.
rewrite O; eauto.
eapply ordertyping_preservation_consts; [eauto|].
intros y ?; rewrite consts_agree.
econstructor.
rewrite <-consts_agree.
Admitted.

Lemma remove_constants_ordertypingSubst Delta sigma Gamma : Delta ⊩(n) sigma : Gamma -> (forall x c, c ∈ consts (sigma x) -> R' c = None -> c ∈ C) -> enc_ctx C Delta ⊩(n) enc_subst C sigma : enc_ctx C Gamma.
Proof using consts_agree O.
intros ?????.
unfold enc_ctx in H1.
rewrite nth_error_map_option in H1.
destruct nth eqn: EQ; try discriminate; injection H1 as <-.
Admitted.

Lemma inv_subst_typing Delta sigma Gamma: Delta ⊩(n) sigma : enc_ctx C Gamma -> Delta ⊩(n) inv_subst C sigma : Gamma.
Proof using consts_agree O.
intros ????.
eapply inv_term_typing, H.
Admitted.

Lemma subst_consts_subst Z (s: exp X) sigma tau theta zeta (kappa: X -> exp Z): (forall x, x ∈ vars s -> sigma • subst_consts zeta (tau x) >* subst_consts kappa (theta x)) -> (forall x, x ∈ consts s -> sigma • zeta x >* kappa x) -> sigma • subst_consts zeta (tau • s) >* subst_consts kappa (theta • s).
Proof using ι n inv_term inv_subst enc_term enc_subst enc_const Y RE R' C.
induction s in sigma, zeta, tau, kappa, theta |-*.
-
cbn; intros; eapply H; now econstructor.
-
cbn; intros; eapply H0; eauto.
-
cbn -[vars]; intros.
rewrite IHs with (kappa := kappa >> ren shift) (theta := up theta); eauto.
+
intros []; cbn; eauto.
unfold funcomp at 2.
rewrite ren_subst_consts_commute.
unfold funcomp at 2.
rewrite ren_subst_consts_commute.
unfold up.
asimpl.
erewrite <-compSubstSubst_exp; try reflexivity.
intros; eapply subst_steps, H.
eauto.
+
intros x.
unfold funcomp.
asimpl.
erewrite <-compSubstSubst_exp; try reflexivity.
intros; eapply subst_steps, H0; eauto.
-
intros; cbn; rewrite IHs1, IHs2; try reflexivity.
1, 3: intros; eapply H; eauto.
Admitted.

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
Admitted.

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
Admitted.

Lemma enc_inv_motivation s: (forall x, x ∈ consts s -> R' x = None -> x ∈ C) -> inv_term C (enc_term C s) >* (fun x => AppR (var x) (map const C)) • s.
Proof using n.
intros H.
replace (enc_term C s) with (var • enc_term C s) by now asimpl.
Admitted.

Definition iConsts {n} (I: orduni n X) := filter (fun x => if R' x == None then true else false) (Consts [s₀; t₀]).
Program Instance remove_constants n (I: orduni n X) (H: ord' (map (ctype X) (iConsts I)) < n) : orduni n Y := { s₀ := enc_term (iConsts I) s₀; t₀ := enc_term (iConsts I) t₀; A₀ := enc_type (iConsts I) A₀; Gamma₀ := enc_ctx (iConsts I) Gamma₀; }.
Next Obligation.
eapply remove_constants_ordertyping; eauto using H1₀.
cbn; simplify; intuition.
Admitted.

Lemma unification_retract_backward n (I: orduni n X): 1 <= n -> OU n Y (unification_retract I) -> OU n X I.
Proof.
intros Leq (Delta & sigma & T & EQ).
pose (C := Consts (map sigma (nats (length Gamma₀)))).
pose (f y := match find y C with | Some x => length Delta + x | None => 0 end).
exists (Delta ++ target' (map (ctype Y) C)).
exists (sigma >> subst_consts (re f)).
split.
-
eapply re_typing; eauto.
intros ???.
eapply weakening_ordertyping_app; eauto.
intros x y H1 H2.
eapply Consts_consts with (S := map sigma (nats (| Gamma₀ |))) in H2; eauto using in_map, lt_nats.
unfold f, C.
eapply find_in in H2 as [? H3]; rewrite H3.
rewrite nth_error_app2; simplify; eauto.
unfold target'; erewrite map_map, map_nth_error; simplify; eauto.
now eapply find_Some.
-
unfold s₀, t₀ in EQ; cbn in EQ.
now rewrite <-!subst_consts_inject_backwards, EQ.
