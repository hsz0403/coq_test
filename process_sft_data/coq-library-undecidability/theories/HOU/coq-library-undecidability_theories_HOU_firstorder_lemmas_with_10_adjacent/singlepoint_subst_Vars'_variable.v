Set Implicit Arguments.
From Equations Require Import Equations.
Require Import List Lia Arith Wf Morphisms Program.Program.
From Undecidability.HOU Require Import unification.unification concon.conservativity calculus.calculus.
Import ListNotations.
Tactic Notation "simplify" := Undecidability.HOU.std.tactics.simplify.
Set Default Proof Using "Type".
Section Update.
Context {X: Const}.
Definition update x v (sigma: fin -> exp X) := fun y => if x == y then v else sigma y.
End Update.
Section LambdaFreeness.
Context {X: Const}.
Inductive lambda_free : exp X -> Prop := | lambda_free_var x: lambda_free (var x) | lambda_free_const c: lambda_free (const c) | lambda_free_app s t: lambda_free s -> lambda_free t -> lambda_free (s t).
End LambdaFreeness.
Hint Constructors lambda_free : core.
Section Unification.
Variable (X: Const).
Implicit Types (Gamma: ctx) (n: nat) (sigma tau: fin -> exp X) (s t: exp X) (E: list (exp X * exp X)).
Variable (free: fin -> Prop) (isFree: Dec1 free).
Definition bound x := ~ free x.
Definition free' sigma := (forall x, bound x -> sigma x = var x) /\ (forall x, free x -> forall y, y ∈ vars (sigma x) -> free y).
Section Decomposition.
Fixpoint decomp s t: option (eqs X) := if s == t then Some nil else match s, t with | var x, t => Some [(var x, t)] | s, var x => Some [(var x, s)] | app s1 s2, app t1 t2 => match decomp s1 t1, decomp s2 t2 with | Some E1, Some E2 => Some (E1 ++ E2) | _, _ => None end | _, _ => None end.
Fixpoint decomp' E := match E with | nil => Some nil | e :: E => match decomp (fst e) (snd e), decomp' E with | Some E1, Some E2 => Some (E1 ++ E2) | _, _ => None end end.
Ltac decomp_ind := match goal with | [|- decomp ?s ?t = Some ?E -> _] => intros H; pattern s, t, E; eapply decomp_some_ind; [idtac..|eapply H]; clear s t E H | [|- decomp ?s ?t = None -> _] => intros H; pattern s, t; eapply decomp_none_ind; [idtac..|eapply H]; clear s t H | [|- decomp' ?E = Some ?E' -> _] => intros H; pattern E, E'; eapply decomp'_some_ind; [idtac..|eapply H]; clear E E' H | [|- decomp' ?E = None -> _] => intros H; pattern E; eapply decomp'_none_ind; [idtac..|eapply H]; clear E H end.
End Decomposition.
Ltac decomp_ind := match goal with | [|- decomp ?s ?t = Some ?E -> _] => intros H; pattern s, t, E; eapply decomp_some_ind; [idtac..|eapply H]; clear s t E H | [|- decomp ?s ?t = None -> _] => intros H; pattern s, t; eapply decomp_none_ind; [idtac..|eapply H]; clear s t H | [|- decomp' ?E = Some ?E' -> _] => intros H; pattern E, E'; eapply decomp'_some_ind; [idtac..|eapply H]; clear E E' H | [|- decomp' ?E = None -> _] => intros H; pattern E; eapply decomp'_none_ind; [idtac..|eapply H]; clear E H end.
Reserved Notation "E ↦ sigma" (at level 80).
Inductive unify E: (fin -> exp X) -> Prop := | unifyId: decomp' E = Some nil -> E ↦ var | unifyStep x s E' sigma: decomp' E = Some ((var x, s) :: E') -> free x -> (forall y, y ∈ vars s -> free y) -> update x s var •₊₊ E' ↦ sigma -> ~ x ∈ vars s -> E ↦ update x (sigma • s) sigma where "E ↦ sigma" := (unify E sigma).
Section Computability.
Definition subvars := MR strict_incl (@Vars' X).
Instance wf_subvars : WellFounded subvars.
Proof.
eapply measure_wf, wf_strict_incl, eq_dec.
Notation "( a ; b )" := (exist _ a b).
Definition remember Y (x : Y) : {y | x = y}.
Proof.
exists x.
reflexivity.
Global Obligation Tactic := idtac.
Equations? unif (E: list (exp X * exp X)) : { sigma | E ↦ sigma } + ({ sigma | E ↦ sigma } -> False) by wf E subvars := unif E with remember (decomp' E) => { unif E (Some nil ; H) := inl (var ; _) ; unif E (Some ((var x, s) :: E') ; H) with (x el vars s, isFree x, dec_all isFree (vars s)) => { unif E (Some ((var x, s) :: E') ; H) (right H1, left H2, left H3) with (unif (update x s var •₊₊ E')) => { unif E (Some ((var x, s) :: E') ; H) (right H1, left H2, left H3) (inl (sigma;_)) := inl (update x (sigma • s) sigma ; _); unif _ _ _ _ := inr _ }; unif E _ _ := inr _ }; unif E _ => inr _ }.
Proof.
all: try now intros [σ H]; inv H; intuition congruence.
-
now econstructor.
-
unfold subvars, MR.
eapply Vars_decomp' in H.
split.
+
rewrite singlepoint_subst_Vars'.
cbn in H.
lauto.
+
exists x.
split.
cbn in H; lauto.
intros ? % singlepoint_subst_Vars'_variable.
intuition.
-
econstructor; eauto.
-
intros [σ H]; inv H.
intuition congruence.
rewrite unknown0 in H0.
inv H0; eauto.
-
intros [σ H]; inv H.
congruence.
rewrite unknown0 in H0.
inv H0; eauto.
End Computability.
Section Unifiability.
Definition unifies sigma s t := sigma • s = sigma • t.
Definition Unifies sigma E := forall e, e ∈ E -> unifies sigma (fst e) (snd e).
Global Instance unifies_equiv sigma: Equivalence (unifies sigma).
Proof.
constructor; unfold unifies; congruence.
Hint Rewrite Unifies_cons : simplify.
Hint Resolve Unifies_nil : core.
Hint Rewrite Unifies_app : simplify.
Definition equi_unifiable (E1 E2: eqs X) := forall sigma, Unifies sigma E1 <-> Unifies sigma E2.
Notation "E1 ≈ E2" := (equi_unifiable E1 E2) (at level 80).
Global Instance equi_unifiable_equivalence: Equivalence equi_unifiable.
Proof.
econstructor; [firstorder.. |].
intros E1 E2 E3 H1 H2 sigma; unfold equi_unifiable in *.
now rewrite H1, H2.
Instance equi_unifiable_app: Proper (equi_unifiable ++> equi_unifiable ++> equi_unifiable) (@List.app (eq X)).
Proof.
intros ?????? sigma; simplify; firstorder.
Hint Resolve equi_unifiable_refl equi_unifiable_app equi_unifiable_comm equi_unifiable_cons equi_unifiable_decompose_app : equi_unifiable.
End Unifiability.
Hint Rewrite Unifies_cons Unifies_app: simplify.
Hint Resolve Unifies_nil : core.
Section Soundness.
Variable (Gamma: ctx).
Hypothesis (HO: ord' Gamma <= 1).
End Soundness.
Section Completeness.
Fixpoint size (s: exp X) := match s with | var x => 0 | const x => 0 | lambda s => S (size s) | app s1 s2 => S(size s1 + size s2) end.
End Completeness.
End Unification.
Section Retyping.
Variable (X: Const).
Arguments s₀ {_} {_} _.
Arguments t₀ {_} {_} _.
Arguments Gamma₀ {_} {_} _.
Arguments A₀ {_} {_} _.
Definition retype_ctx (n: nat) (Gamma : ctx) := map (fun A => if dec2 le (ord A) n then A else alpha) Gamma.
Fixpoint retype_type (n: nat) (A : type) := match A with | typevar beta => typevar beta | A → B => (if dec2 le (ord A) n then A else alpha) → retype_type n B end.
Instance retype n (I: orduni n X) : orduni n X.
Proof.
refine {| Gamma₀ := retype_ctx n (Gamma₀ I); s₀ := eta₀ (s₀ I) H1₀; t₀ := eta₀ (t₀ I) H2₀; A₀ := retype_type n (A₀ I) |}.
-
abstract (eapply normal_retyping; [apply eta₀_normal | apply eta₀_typing]).
-
abstract (eapply normal_retyping; [apply eta₀_normal | apply eta₀_typing]).
Defined.
End Retyping.
Section FirstOrderDecidable.
Variable (X: Const).
Implicit Types (Gamma: ctx) (n: nat) (sigma tau: fin -> exp X) (s t: exp X) (E: list (exp X * exp X)).
Let free (k: nat) (x: nat) := x >= k.
Instance dec_free k: Dec1 (free k).
Proof.
unfold free; typeclasses eauto.
Definition decr (k: nat) (sigma: fin -> exp X) (x: nat) := ren (fun y => y - k) (sigma (x + k)).
End FirstOrderDecidable.

Lemma singlepoint_subst_vars x s t: vars (update x s var • t) ⊆ vars s ++ vars t.
Proof.
intros ? (y & H1 & H2) % vars_varof % varof_subst.
unfold update in *; destruct eq_dec; subst.
eapply varof_vars in H2; simplify; eauto.
inv H2.
Admitted.

Lemma singlepoint_subst_vars_variable x s t: x ∈ vars (update x s var • t) -> x ∈ vars s /\ x ∈ vars t.
Proof.
intros (y & ? & ?) % vars_varof % varof_subst.
unfold update in *; destruct eq_dec; subst; split; eauto using varof_vars.
Admitted.

Lemma singlepoint_subst_Vars' x s E: Vars' (update x s var •₊₊ E) ⊆ vars s ++ Vars' E.
Proof.
induction E as [|[u v]]; [cbn; easy|]; simplify.
cbn; rewrite !singlepoint_subst_vars, IHE, <-!app_assoc.
repeat eapply incl_app_build.
Admitted.

Lemma update_irrelevant x s t sigma: ~ x ∈ vars t -> update x s sigma • t = sigma • t.
Proof.
intros H; eapply subst_extensional; intros y.
Admitted.

Lemma update_typing n Delta Gamma sigma (s: exp X) x A: Delta ⊩(n) sigma : Gamma -> Delta ⊢(n) s : A -> nth Gamma x = Some A -> Delta ⊩(n) update x s sigma : Gamma.
Proof.
Admitted.

Lemma lambda_free_AppR s T: lambda_free s -> (forall t, t ∈ T -> lambda_free t) -> lambda_free (AppR s T).
Proof.
Admitted.

Lemma ordertyping_one_atom Gamma (s: exp X) A: Gamma ⊢ s : A -> nf s -> ord A <= 1 -> isAtom (head s).
Proof.
destruct 2; subst; intros.
destruct k; cbn; simplify; eauto.
inv H.
Admitted.

Lemma order_one_lambda_free Gamma s A: normal s -> (Gamma ⊢(1) s : A) -> isAtom (head s) -> lambda_free s.
Proof.
intros N % normal_nf.
induction N in Gamma, A |-*; subst.
destruct k; cbn;[intros|easy].
simplify in H1.
eapply lambda_free_AppR.
-
destruct s; cbn in i; intuition econstructor.
-
eapply AppR_ordertyping_inv in H0 as H4; destruct H4 as [L H4].
intuition.
assert (ord' L <= 1).
+
destruct s; cbn in i.
3-4:intuition.
*
inv H3.
simplify in H6.
lia.
*
inv H3.
rewrite H6 in H7.
simplify in H7.
lia.
+
eapply orderlisttyping_element in H2 as [B []].
2:now eauto.
eapply H; eauto.
eapply ordertyping_one_atom; eauto.
Admitted.

Lemma lambda_free_subst Delta (sigma: fin -> exp X) x A: (Delta ⊢(1) sigma x : A) -> ord A <= 1 -> normal (sigma x) -> lambda_free (sigma x).
Proof.
intros H1 H3 H4; eapply order_one_lambda_free; eauto.
eapply head_atom; eauto.
destruct sigma; cbn; intuition.
inv H1.
Admitted.

Lemma lambda_free_not_lam s: lambda_free s -> ~ isLam s.
Proof.
Admitted.

Lemma lambda_free_substitution sigma s: lambda_free s -> (forall x, x ∈ vars s -> lambda_free (sigma x)) -> lambda_free (sigma • s).
Proof.
induction 1; cbn; eauto using lambda_free.
Admitted.

Lemma lambda_free_subst_eqs sigma E: (forall x, x ∈ Vars' E -> lambda_free (sigma x)) -> all_terms lambda_free E -> all_terms lambda_free (sigma •₊₊ E).
Proof.
intros H; induction E as [| [s t]]; cbn; eauto; simplify; cbn in *.
intros (H1 & H2 & H3).
split; [|split].
1 - 2: eapply lambda_free_substitution; eauto; intros; eapply H; intuition.
Admitted.

Lemma lambda_free_normal s: lambda_free s -> normal s.
Proof.
induction 1; [ eauto.. |].
eapply normal_app_intro; eauto.
Admitted.

Lemma singlepoint_subst_Vars'_variable x s E: x ∈ Vars' (update x s var •₊₊ E) -> x ∈ vars s /\ x ∈ Vars' E.
Proof.
induction E as [|[u v]]; [cbn; intuition|]; simplify.
cbn; simplify; intros [[H % singlepoint_subst_vars_variable | H % singlepoint_subst_vars_variable] | H].
all:tauto.
