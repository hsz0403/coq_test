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

Lemma unifies_not_var x s tau: var x <> s -> unifies tau (var x) s -> ~ x ∈ vars s.
Proof.
intros H1; unfold unifies; cbn; intros S % (f_equal size).
rewrite size_subst in S.
intros H; eapply H1; eapply in_map with (f := tau >> size) in H as H'.
eapply Sum_in in H'.
eapply vars_varof in H; inv H; cbn in *; eauto.
Admitted.

Lemma unifies_free sigma x s: ~ x ∈ vars s -> free' sigma -> unifies sigma (var x) s -> free x.
Proof using isFree.
intros H1 F H2; unfold unifies in *; cbn in *.
destruct F as [F1 F2].
destruct (isFree x) as [H|H]; eauto.
eapply F1 in H as H'.
rewrite H' in H2.
destruct s; try discriminate; cbn in H2.
destruct (isFree f) as [L|L]; eauto.
-
eapply F2 with (y := x) in L; eauto; rewrite <-H2; cbn; intuition.
-
Admitted.

Lemma unifies_free_all sigma x s: ~ x ∈ vars s -> free' sigma -> free x -> unifies sigma (var x) s -> (forall y, y ∈ vars s -> free y) .
Proof using isFree.
intros H1 F H2 H3 y H4; unfold unifies in *; cbn in *.
destruct F as [F1 F2].
destruct (isFree y) as [H|H]; eauto.
specialize (F2 _ H2) as H5.
rewrite H3 in H5.
eapply H5.
eapply subst_vars.
eauto.
rewrite F1.
cbn; eauto.
Admitted.

Lemma decomp_irrefl s t E: decomp s t = Some E -> forall u v, (u,v) ∈ E -> u <> v.
Proof.
decomp_ind; cbn.
all: intuition idtac; simplify in *; try congruence.
Admitted.

Lemma decomp'_irrefl E E': decomp' E = Some E' -> forall u v, (u,v) ∈ E' -> u <> v.
Proof.
decomp_ind.
all: intuition idtac; simplify in *.
Admitted.

Lemma eqs_size_induction P: (forall E, (forall E' x, Vars' E' ⊆ Vars' E -> x ∈ Vars' E -> ~ x ∈ Vars' E' -> P E') -> P E) -> forall E, P E.
Proof.
intros IH E.
eapply well_founded_induction_type.
eapply measure_wf, wf_strict_incl with (X := nat); typeclasses eauto.
intros x H; eapply IH; intros; eapply H.
Admitted.

Lemma unify_complete sigma E: free' sigma -> Unifies sigma E -> all_terms (@lambda_free X) E -> exists tau, E ↦ tau.
Proof using isFree.
intros F; induction E as [E IH] using eqs_size_induction; intros U LF.
destruct (decomp' E) as [[| [t s] E']|] eqn: DE.
-
exists var.
now econstructor.
-
eapply decomp'_some_var in DE as H'; cbn in H'; destruct H' as [x ->].
eapply equi_unifiable_decomp' in DE as U'.
eapply U' in U as H4; simplify in H4; destruct H4 as [H4 H5]; cbn in H4.
eapply unifies_not_var in H4 as H6; [| eapply decomp'_irrefl; eauto; firstorder].
eapply unifies_free in H6 as H7; eauto.
specialize (unifies_free_all H6 F H7 H4) as H8.
eapply Vars_decomp' in DE as H9; simplify in H9; cbn in H9.
assert (Vars' (update x s var •₊₊ E') ⊆ Vars' E) by (rewrite singlepoint_subst_Vars'; eapply incl_cons_project_r; eauto).
destruct (IH (update x s var •₊₊ E') x) as [tau]; eauto.
+
eapply H9; firstorder.
+
intros ? % singlepoint_subst_Vars'_variable; intuition.
+
rewrite equi_unifiable_cons in U'.
eapply U' in U; simplify in U; intuition.
+
eapply decomp'_lambda_free in DE; eauto; simplify in DE; eauto.
eapply lambda_free_subst_eqs; intuition idtac; eauto.
unfold update; destruct eq_dec; intuition; eauto using lambda_free.
+
exists (update x (tau • s) tau); econstructor; eauto.
-
eapply decomp'_none_not_unifiable in DE; intuition eauto.
Admitted.

Lemma retype_ctx_ord n Gamma: 1 <= n -> ord' (retype_ctx n Gamma) <= n.
Proof.
intros H; induction Gamma; cbn; eauto; unfold retype_ctx in *.
Admitted.

Lemma retype_type_ord n A: 1 <= n -> ord (retype_type n A) <= S n.
Proof.
intros H; induction A; cbn [retype_type].
-
cbn; lia.
-
Admitted.

Lemma retype_type_id n A: ord A <= S n -> retype_type n A = A.
Proof.
induction A; cbn [retype_type]; simplify; intuition.
Admitted.

Lemma retype_Arr n L A: retype_type n (Arr L A) = Arr (retype_ctx n L) (retype_type n A).
Proof.
Admitted.

Lemma normal_retyping n Gamma (s: exp X) A: normal s -> Gamma ⊢(n) s : A -> retype_ctx n Gamma ⊢(n) s : retype_type n A.
Proof.
intros H % normal_nf; induction H in Gamma, A |-*; subst.
intros (L & B & ? & -> & ?) % Lambda_ordertyping_inv.
rewrite retype_Arr.
eapply Lambda_ordertyping; [unfold retype_ctx; now simplify|].
unfold retype_ctx; rewrite <-map_rev, <-map_app; fold (retype_ctx n (rev L ++ Gamma)).
eapply AppR_ordertyping_inv in H0 as (L' & ? & ?).
assert (ord' L' <= n).
-
destruct s; destruct i; inv H2; simplify in H4.
intuition.
rewrite H4 in H5; simplify in H5; intuition.
-
eapply AppR_ordertyping with (L0 := retype_ctx n L').
+
clear H2.
induction H0; eauto.
econstructor.
all: cbn in H3; simplify in H3.
2:intuition.
destruct dec2; intuition.
erewrite <-retype_type_id; [| transitivity n; eauto].
eapply H; cbn; intuition.
+
unfold retype_ctx at 2; rewrite <-map_rev; fold (retype_ctx n (rev L')).
rewrite <-retype_Arr.
destruct s; destruct i.
all: inv H2; rewrite retype_type_id.
2-4:eauto.
econstructor; eauto.
unfold retype_ctx; erewrite map_nth_error; eauto.
Admitted.

Instance retype n (I: orduni n X) : orduni n X.
Proof.
refine {| Gamma₀ := retype_ctx n (Gamma₀ I); s₀ := eta₀ (s₀ I) H1₀; t₀ := eta₀ (t₀ I) H2₀; A₀ := retype_type n (A₀ I) |}.
-
abstract (eapply normal_retyping; [apply eta₀_normal | apply eta₀_typing]).
-
Admitted.

Lemma retype_iff n (I: orduni n X): 1 <= n -> OU n X I <-> OU n X (@retype n I).
Proof.
intros Leq.
rewrite orduni_normalise_correct.
destruct I as [Gamma s t A ? ?]; unfold orduni_normalise, retype, OU; cbn.
split; intros (Delta & sigma & ? & ?); eapply conservativity.ordertyping_weak_ordertyping.
1,3,4,6:now eauto.
all: intros ??; simplify; intros ? [H'|H']; eapply H.
all: rewrite nth_error_map_option in *.
all: destruct (nth Gamma x) eqn: N; try discriminate; cbn in *.
all: destruct dec2 as [|L]; eauto.
all: exfalso; eapply L.
Admitted.

Instance dec_free k: Dec1 (free k).
Proof.
Admitted.

Lemma decr_lambda_free k sigma: (forall x, lambda_free (sigma x)) -> (forall x, lambda_free (decr k sigma x)).
Proof.
intros H x; unfold decr; asimpl.
Admitted.

Lemma FO_subst_equiv_eq Delta sigma Gamma (s t: exp X) A: (Delta ⊩(1) sigma : Gamma) -> (forall x, normal (sigma x)) -> normal s -> normal t -> (Gamma ⊢(1) s : A) -> (Gamma ⊢(1) t : A) -> sigma • s ≡ sigma • t -> sigma • s = sigma • t.
Proof.
intros.
rewrite !subst_extensional with (sigma0 := sigma) (tau := fun x => if x el (vars s ++ vars t) then sigma x else var x).
2 - 3: intros; edestruct dec_in as [D|D]; simplify in D; intuition.
eapply equiv_unique_normal_forms.
intuition.
1: rewrite !subst_extensional with (tau := sigma) (sigma0 := fun x => if x el (vars s ++ vars t) then sigma x else var x); eauto.
1 - 2: intros; edestruct dec_in as [D|D]; simplify in D; intuition.
all: eapply normal_subst; eauto 2; intros x; destruct dec_in; eauto 2.
all: simplify in i; destruct i as [V|V]; eapply vars_ordertyping in V as V'; eauto 2.
all: destruct V' as (B & V1 & V2).
Admitted.

Lemma decr_typing L Gamma n sigma: free' (free (length L)) sigma -> L ++ Gamma ⊩(n) sigma : L ++ Gamma -> Gamma ⊩(n) decr (length L) sigma : Gamma.
Proof.
intros ? ? x A ?; unfold decr.
destruct H as [F1 F2].
eapply ordertyping_weak_preservation_under_renaming with (Gamma0 := L ++ Gamma).
-
eapply H0.
rewrite nth_error_app2; simplify; eauto.
-
intros y B H ?.
eapply F2 in H2; unfold free in *; eauto.
Admitted.

Lemma decr_unifies sigma (s t: exp X) k: unifies sigma s t -> free' (free k) sigma -> unifies (decr k sigma) (Lambda k s) (Lambda k t).
Proof.
intros H1 [H2 H3]; unfold unifies in *; asimpl; f_equal.
erewrite subst_extensional.
symmetry.
erewrite subst_extensional; eauto.
all: intros x V; destruct (le_lt_dec k x).
1, 3: rewrite it_up_ge; eauto; unfold decr; asimpl.
1 - 2: rewrite Nat.sub_add; eauto; asimpl; rewrite subst_extensional with (tau := var); [now asimpl|].
1 - 2: intros y ? % H3; unfold free in *; eauto; unfold funcomp; f_equal; lia.
Admitted.

Lemma it_up_free' k (sigma: fin -> exp X): free' (free k) (it k up sigma).
Proof.
unfold free; split; intros x; unfold bound.
-
intros ?; rewrite it_up_lt; intuition.
lia.
-
intros ? y.
rewrite it_up_ge; eauto.
Admitted.

Lemma firstorder_decidable: Dec1 (OU 1 X).
Proof.
intros I.
eapply iff_dec.
eapply retype_iff; eauto.
eapply iff_dec.
eapply OU_NOU; eauto.
Admitted.

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
