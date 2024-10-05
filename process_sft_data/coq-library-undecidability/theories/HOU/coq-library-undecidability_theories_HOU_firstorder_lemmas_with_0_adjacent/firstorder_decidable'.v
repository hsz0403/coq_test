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

Lemma firstorder_decidable' (I: orduni 1 X): ord' Gamma₀ <= 1 -> ord A₀ <= 2 -> normal s₀ -> normal t₀ -> Dec (NOU 1 I).
Proof.
intros O1 O2 N1 N2; eapply iff_dec with (P := exists Delta sigma, Delta ⊩(1) sigma : Gamma₀ /\ sigma • s₀ = sigma • t₀ /\ (forall x : fin, normal (sigma x))).
split; intros (Delta & sigma & ?); exists Delta; exists sigma; intuition idtac; eauto 2 using FO_subst_equiv_eq, eq_equiv.
destruct I as [Gamma s t A H1 H2]; cbn in *; subst.
unfold NOU; cbn in *.
eapply normal_nf in N1 as N1'; destruct N1' as [k1 s ? ? ? ? ->].
eapply normal_nf in N2 as N2'; destruct N2' as [k2 t ? ? ? ? ->].
eapply normal_Lambda in N1.
eapply normal_Lambda in N2.
destruct (k1 == k2) as [H4|H4]; [subst; destruct (@unif _ (fun x => x >= k2) _ [(AppR s T, AppR t T0)]) as [[sigma H']|H']|].
1: left.
2: right.
3: right.
all: eapply Lambda_ordertyping_inv in H1 as (L & B & ? & ? & ?).
all: eapply Lambda_ordertyping_inv in H2 as (L' & B' & ? & ? & ?); subst.
1, 2: assert (L = L' /\ B = B') as []; [|subst L' B'; clear H3 H4].
1, 3: try (clear H'); eapply Arr_inversion in H3 as [? []]; try lia; rewrite ?H4; eauto 2; destruct x; cbn in *; simplify in H0; eauto 2; subst; simplify in H4; cbn in H4; lia.
all: simplify in O2; cbn in O2; destruct O2 as [O2 _]; eapply le_S_n in O2.
all: assert (ord' (rev L ++ Gamma) <= 1) by now simplify.
all: eapply order_one_lambda_free in N1 as L1; simplify; eauto 2.
all: eapply order_one_lambda_free in N2 as L2; simplify; eauto 2.
+
eapply unify_free' in H' as P.
eapply unify_typing with (Gamma := rev L ++ Gamma) (L := [B]) in H' as T2; [| eauto|simplify; cbn; intuition idtac; eauto using all_terms_nil|eauto using eqs_ordertyping].
specialize (unify_lambda_free H') as LF; mp LF; simplify; intuition idtac; eauto using all_terms_nil.
exists Gamma.
exists (decr (length L) sigma).
intuition idtac.
*
specialize decr_typing with (L := rev L) as H9; simplify in H9; eauto.
*
eapply decr_unifies; eauto.
specialize (unify_unifiable H' (AppR s T, AppR t T0)); cbn; intuition.
*
eapply lambda_free_normal.
pose proof (free := fun (k: nat) (x: nat) => x >= k).
eapply decr_lambda_free; intros; eapply LF.
+
intros (Delta & sigma & E1 & E2 & E3).
asimpl in E2.
eapply Lambda_injective in E2.
edestruct unify_complete with (sigma := it (|L|) up sigma) (E := [(AppR s T,AppR t T0)]) (free := free (|L|)); eauto.
*
typeclasses eauto.
*
eapply it_up_free'.
*
rewrite Unifies_cons.
cbn; unfold unifies; asimpl; asimpl in E2; intuition eauto using Unifies_nil.
*
simplify; eauto using all_terms_nil.
+
intros (Delta & sigma & ? & ? & ?).
assert (|L| < |L'| \/ |L'| < |L|) as [LT|LT] by lia.
2: symmetry in H3.
all: eapply Arr_inversion in H3 as [L''].
2,4:intuition.
all:intuition idtac;subst.
all: simplify in H5; asimpl in H5; rewrite <-Lambda_plus in H5.
all: eapply Lambda_injective in H5; destruct L''; [ simplify in LT; try lia; cbn in H5 | ].
1: destruct T; destruct s; cbn in H5; try discriminate; [| destruct i].
2: destruct T0; destruct t; cbn in H5; try discriminate; [| destruct i0].
all: try destruct (le_lt_dec (length L') f); try destruct (le_lt_dec (length L) f).
2, 4: rewrite it_up_lt in H5; try discriminate;eauto 2.
1: inv H.
2: inv H2.
all: cbn [Arr] in H7; now eapply ord_arr_one in H7.
