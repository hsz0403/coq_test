From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Coq.Vectors.Vector.
Local Notation vec := t.
From Undecidability Require Export FOL.Util.Syntax.
Require Import Equations.Equations.
Section fix_signature.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type := | Forall_nil : Forall P (@Vector.nil A) | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).
Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type := | vec_inB {n} (v : t A n) : vec_in a (cons A a n v) | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
Hint Constructors vec_in : core.
Fixpoint size {ff : falsity_flag} (phi : form) := match phi with | atom _ _ => 0 | falsity => 0 | bin b phi psi => S (size phi + size psi) | quant q phi => S (size phi) end.
Derive Signature for form.
End fix_signature.
Section Subst.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
End Subst.
Section Bounded.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Inductive bounded_t n : term -> Prop := | bounded_var x : n > x -> bounded_t n $x | bouded_func f v : (forall t, Vector.In t v -> bounded_t n t) -> bounded_t n (func f v).
Inductive bounded : forall {ff}, nat -> form ff -> Prop := | bounded_atom ff n P v : (forall t, Vector.In t v -> bounded_t n t) -> @bounded ff n (atom P v) | bounded_bin binop ff n phi psi : @bounded ff n phi -> @bounded ff n psi -> @bounded ff n (bin binop phi psi) | bounded_quant quantop ff n phi : @bounded ff (S n) phi -> @bounded ff n (quant quantop phi) | bounded_falsity n : @bounded falsity_on n falsity.
Arguments bounded {_} _ _.
Definition bounded_L {ff : falsity_flag} n A := forall phi, phi el A -> bounded n phi.
Derive Signature for In.
End Bounded.
Ltac solve_bounds := repeat constructor; try lia; try inversion X; intros; match goal with | H : Vector.In ?x (@Vector.cons _ ?y _ ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H | H : Vector.In ?x (@Vector.nil _) |- _ => try inversion H | _ => idtac end.
Require Import EqdepFacts.
Ltac resolve_existT := try match goal with | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)] end.
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
intros v.
refine (dec_vec_in _ _ _ _).
Section EqDec.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Hypothesis eq_dec_Funcs : eq_dec syms.
Hypothesis eq_dec_Preds : eq_dec preds.
Hypothesis eq_dec_binop : eq_dec binop.
Hypothesis eq_dec_quantop : eq_dec quantop.
Global Instance dec_term : eq_dec term.
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
intros t.
induction t as [ | ]; intros [|? v']...
-
decide (x = n)...
-
decide (F = f)...
destruct (dec_vec_in _ _ _ X v')...
Instance dec_falsity : eq_dec falsity_flag.
Proof.
intros b b'.
unfold dec.
decide equality.
Global Instance dec_form {ff : falsity_flag} : eq_dec form.
Proof.
intros phi psi.
destruct (dec_form_dep phi psi); rewrite eq_dep_falsity in *; firstorder.
End EqDec.
Section Enumerability.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Variable list_Funcs : nat -> list syms.
Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.
Variable list_Preds : nat -> list preds.
Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.
Variable list_binop : nat -> list binop.
Hypothesis enum_binop' : list_enumerator__T list_binop binop.
Variable list_quantop : nat -> list quantop.
Hypothesis enum_quantop' : list_enumerator__T list_quantop quantop.
Fixpoint vecs_from X (A : list X) (n : nat) : list (vec X n) := match n with | 0 => [Vector.nil X] | S n => [ Vector.cons X x _ v | (x, v) ∈ (A × vecs_from X A n) ] end.
Fixpoint L_term n : list term := match n with | 0 => [] | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from _ (L_term n) (ar_syms F) ] | F ∈ L_T n]) end.
Fixpoint L_form {ff : falsity_flag} n : list form := match n with | 0 => match ff with falsity_on => [falsity] | falsity_off => [] end | S n => L_form n ++ concat ([ [ atom P v | v ∈ vecs_from _ (L_term n) (ar_preds P) ] | P ∈ L_T n]) ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ L_T n]) ++ concat ([ [ quant op phi | phi ∈ L_form n ] | op ∈ L_T n]) end.

Lemma term_rect (p : term -> Type) : (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
Proof.
intros f1 f2.
eapply term_rect'.
-
apply f1.
-
intros.
apply f2.
intros t.
induction 1; inversion X; subst; eauto.
apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto.
Admitted.

Lemma term_ind (p : term -> Prop) : (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
Proof.
intros f1 f2.
eapply term_rect'.
-
apply f1.
-
intros.
apply f2.
intros t.
induction 1; inversion X; subst; eauto.
apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto.
Admitted.

Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) : (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
Proof.
intros H x.
apply H.
induction (f x).
-
intros y.
lia.
-
intros y.
intros [] % Lt.le_lt_or_eq.
+
apply IHn; lia.
+
apply H.
injection H0.
Admitted.

Lemma subst_size {ff : falsity_flag} rho phi : size (subst_form rho phi) = size phi.
Proof.
Admitted.

Lemma form_ind_subst : forall P : form -> Prop, P falsity -> (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) -> (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) -> (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) -> forall (f4 : form), P f4.
Proof.
intros P H1 H2 H3 H4 phi.
induction phi using (@size_ind _ size).
depelim phi; trivial.
-
injection H.
intros -> % Eqdep_dec.inj_pair2_eq_dec; trivial.
decide equality.
-
apply H3; apply H; cbn; lia.
-
apply H4.
intros sigma.
apply H.
cbn.
rewrite subst_size.
Admitted.

Lemma subst_term_ext (t : term) sigma tau : (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
Proof.
intros H.
induction t; cbn.
-
now apply H.
-
f_equal.
Admitted.

Lemma subst_term_id (t : term) sigma : (forall n, sigma n = var n) -> t`[sigma] = t.
Proof.
intros H.
induction t; cbn.
-
now apply H.
-
f_equal.
Admitted.

Lemma subst_term_var (t : term) : t`[var] = t.
Proof.
Admitted.

Lemma subst_term_comp (t : term) sigma tau : t`[sigma]`[tau] = t`[sigma >> subst_term tau].
Proof.
induction t; cbn.
-
reflexivity.
-
f_equal.
rewrite map_map.
Admitted.

Lemma subst_term_shift (t : term) s : t`[↑]`[s..] = t.
Proof.
rewrite subst_term_comp.
apply subst_term_id.
Admitted.

Lemma up_term (t : term) xi : t`[↑]`[up xi] = t`[xi]`[↑].
Proof.
rewrite !subst_term_comp.
apply subst_term_ext.
Admitted.

Lemma up_ext sigma tau : (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
Proof.
destruct n; cbn; trivial.
unfold funcomp.
Admitted.

Lemma up_var sigma : (forall n, sigma n = var n) -> forall n, up sigma n = var n.
Proof.
destruct n; cbn; trivial.
unfold funcomp.
Admitted.

Lemma up_funcomp sigma tau : forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
Proof.
intros [|]; cbn; trivial.
setoid_rewrite subst_term_comp.
apply subst_term_ext.
Admitted.

Lemma subst_ext {ff : falsity_flag} (phi : form) sigma tau : (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
Proof.
induction phi in sigma, tau |- *; cbn; intros H.
-
reflexivity.
-
f_equal.
apply map_ext.
intros s.
now apply subst_term_ext.
-
now erewrite IHphi1, IHphi2.
-
erewrite IHphi; trivial.
Admitted.

Lemma subst_id {ff : falsity_flag} (phi : form) sigma : (forall n, sigma n = var n) -> phi[sigma] = phi.
Proof.
induction phi in sigma |- *; cbn; intros H.
-
reflexivity.
-
f_equal.
erewrite map_ext; try apply map_id.
intros s.
now apply subst_term_id.
-
now erewrite IHphi1, IHphi2.
-
erewrite IHphi; trivial.
Admitted.

Lemma subst_var {ff : falsity_flag} (phi : form) : phi[var] = phi.
Proof.
Admitted.

Lemma subst_comp {ff : falsity_flag} (phi : form) sigma tau : phi[sigma][tau] = phi[sigma >> subst_term tau].
Proof.
induction phi in sigma, tau |- *; cbn.
-
reflexivity.
-
f_equal.
rewrite map_map.
apply map_ext.
intros s.
apply subst_term_comp.
-
now rewrite IHphi1, IHphi2.
-
rewrite IHphi.
f_equal.
Admitted.

Lemma subst_shift {ff : falsity_flag} (phi : form) s : phi[↑][s..] = phi.
Proof.
rewrite subst_comp.
apply subst_id.
Admitted.

Lemma up_form {ff : falsity_flag} xi psi : psi[↑][up xi] = psi[xi][↑].
Proof.
rewrite !subst_comp.
apply subst_ext.
Admitted.

Lemma term_rect' (p : term -> Type) : (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
Proof.
intros f1 f2.
fix strong_term_ind' 1.
destruct t as [n|F v].
-
apply f1.
-
apply f2.
induction v.
+
econstructor.
+
econstructor.
now eapply strong_term_ind'.
eauto.
