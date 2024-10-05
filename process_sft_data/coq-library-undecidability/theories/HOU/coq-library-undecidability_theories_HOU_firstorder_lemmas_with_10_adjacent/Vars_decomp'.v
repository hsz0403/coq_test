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

Lemma decomp_some_ind (P: exp X -> exp X -> eqs X -> Type): (forall s, P s s nil) -> (forall x s, var x <> s -> P (var x) s [(var x, s)]) -> (forall x s, var x <> s -> P s (var x) [(var x, s)]) -> (forall s1 s2 t1 t2 E1 E2, s1 s2 <> t1 t2 -> decomp s1 t1 = Some E1 -> P s1 t1 E1 -> decomp s2 t2 = Some E2 -> P s2 t2 E2 -> P (s1 s2) (t1 t2) (E1 ++ E2)) -> forall s t E, decomp s t = Some E -> P s t E.
Proof.
intros H1 H2 H3; induction s; intros [] E; cbn.
all: destruct eq_dec as [EQ|NEQ]; try discriminate.
1 - 11: injection 1 as ?; subst E; eauto.
1 - 4: injection EQ; intros; subst; eauto.
destruct (decomp s1 e) eqn: EQ1; try discriminate.
destruct (decomp s2 e0) eqn: EQ2; try discriminate.
injection 1 as ?; subst.
Admitted.

Lemma decomp_none_ind (P: exp X -> exp X -> Type): (forall x t, const x <> t -> ~ isVar t -> P (const x) t) -> (forall x t, const x <> t -> ~ isVar t -> P t (const x)) -> (forall s t, lambda s <> t -> P (lambda s) t) -> (forall s t, s <> lambda t -> P s (lambda t)) -> (forall s1 s2 t1 t2, s1 s2 <> t1 t2 -> P s1 t1 -> P (s1 s2) (t1 t2)) -> (forall s1 s2 t1 t2, s1 s2 <> t1 t2 -> P s2 t2 -> P (s1 s2) (t1 t2)) -> forall s t, decomp s t = None -> P s t.
Proof.
intros H1 H2 H3 H4 IH1 IH2 s t; induction s in t |-*; cbn.
all: destruct eq_dec; try discriminate.
all: destruct t; try discriminate; eauto.
destruct decomp eqn: D1; [destruct (decomp s2 t2) eqn: D2|]; try discriminate.
Admitted.

Lemma decomp'_some_ind (P: eqs X -> eqs X -> Prop): P nil nil -> (forall s t E E1 E2, decomp s t = Some E1 -> decomp' E = Some E2 -> P E E2 -> P ((s, t) :: E) (E1 ++ E2)) -> forall E E', decomp' E = Some E' -> P E E'.
Proof.
intros H IH; induction E as [| [s t]]; cbn.
-
now injection 1 as <-.
-
intros E'; destruct decomp eqn: H1; destruct decomp' eqn: H2; try discriminate.
Admitted.

Lemma decomp'_none_ind (P: eqs X -> Type): (forall E s t, decomp s t = None -> P ((s, t) :: E)) -> (forall E s t, P E -> P ((s, t) :: E)) -> forall E, decomp' E = None -> P E.
Proof.
intros H IH; induction E as [| [s t]]; cbn; try discriminate.
destruct decomp eqn: EQ1; [destruct decomp' eqn: EQ2 |]; try discriminate.
all: intros _.
eapply IH; intuition.
Admitted.

Lemma decomp_some_head_consts s t E x y: decomp s t = Some E -> head s = const x -> head t = const y -> x = y.
Proof.
decomp_ind; eauto.
Admitted.

Lemma decomp_typing s t E Gamma: decomp s t = Some E -> forall A, lambda_free s -> lambda_free t -> (Gamma ⊢(1) s : A) -> (Gamma ⊢(1) t : A) -> exists L, Gamma ⊢₊₊(1) E : L.
Proof.
decomp_ind; intros.
-
exists nil; econstructor.
-
exists [A]; eauto using eqs_ordertyping.
-
exists [A]; eauto using eqs_ordertyping.
-
inv H4.
inv H5.
inv H6.
inv H7.
enough (A0 → A = A1 → A) as H4.
injection H4 as ->.
edestruct H1 as [L1]; eauto.
edestruct H3 as [L2]; eauto.
exists (L1 ++ L2).
eapply ordertyping_combine; unfold left_side, right_side; simplify.
1 - 2: eapply orderlisttyping_app; try eapply left_ordertyping; try eapply right_ordertyping; eauto.
eapply lambda_free_normal in H10 as H10'; eapply lambda_free_not_lam in H10 as H10''.
eapply lambda_free_normal in H9 as H9'; eapply lambda_free_not_lam in H9 as H9''.
eapply head_atom in H10' as H10'''; eauto.
eapply head_atom in H9' as H9'''; eauto.
destruct (head_decompose s1) as [S1].
destruct (head_decompose t1) as [T1].
destruct (head s1); cbn in *;[ | | now intuition..];[| destruct (head t1)]; cbn in *.
4,5:now intuition.
1: subst s1; eapply AppR_ordertyping_inv in H8 as (L & ? & V); inv V.
2: subst t1; eapply AppR_ordertyping_inv in H6 as (L & ? & V); inv V.
1: rewrite ord_Arr in H8; eapply Nat.max_lub_r, ord_arr_one in H8 as [].
1: rewrite ord_Arr in H7; eapply Nat.max_lub_r, ord_arr_one in H7 as [].
eapply decomp_some_head_consts in H0; subst; simplify; cbn; eauto.
subst.
eapply AppR_ordertyping_inv in H8 as (L1 & ? & ?).
eapply AppR_ordertyping_inv in H6 as (L2 & ? & ?).
inv H4.
inv H6.
rewrite H7 in H8.
change (A0 → A) with (Arr [A0] A) in H8.
change (A1 → A) with (Arr [A1] A) in H8.
rewrite <-!Arr_app in H8.
eapply Arr_left_injective in H8.
eapply app_injective_right in H8.
2:now intuition.
Admitted.

Lemma decomp_lambda_free s t E: decomp s t = Some E -> lambda_free s -> lambda_free t -> all_terms (@lambda_free X) E.
Proof.
decomp_ind; intros; eauto; simplify; cbn; eauto using all_terms_nil.
Admitted.

Lemma decomp'_typing Gamma E E': decomp' E = Some E' -> forall L, all_terms (@lambda_free X) E -> Gamma ⊢₊₊(1) E : L -> exists L, Gamma ⊢₊₊(1) E' : L.
Proof.
decomp_ind; eauto.
intros s t E E1 E2 H H' IH L LF T.
inv T.
simplify in LF; intuition.
eapply decomp_typing in H as [L1]; eauto.
edestruct IH as [L2]; eauto.
exists (L1 ++ L2).
eapply ordertyping_combine; unfold left_side, right_side; simplify.
1 - 2: eapply orderlisttyping_app; try eapply left_ordertyping; try eapply right_ordertyping.
Admitted.

Lemma decomp'_lambda_free E E': decomp' E = Some E' -> all_terms (@lambda_free X) E -> all_terms (@lambda_free X) E'.
Proof.
decomp_ind; intros; eauto; simplify in *; intuition.
Admitted.

Lemma vars_decomp s t E: decomp s t = Some E -> Vars' E ⊆ vars s ++ vars t.
Proof.
decomp_ind; cbn; intros; simplify.
1-2:easy.
now intros ? [->|];eauto using in_or_app,in_eq.
rewrite H1, H3.
(repeat eapply incl_app_build); intros ?; simplify.
Admitted.

Instance wf_subvars : WellFounded subvars.
Proof.
Admitted.

Definition remember Y (x : Y) : {y | x = y}.
Proof.
exists x.
Admitted.

Lemma Unifies_cons sigma e E: Unifies sigma (e :: E) <-> unifies sigma (fst e) (snd e) /\ Unifies sigma E.
Proof.
Admitted.

Lemma Unifies_nil sigma: Unifies sigma nil.
Proof.
Admitted.

Lemma Unifies_app sigma E1 E2: Unifies sigma (E1 ++ E2) <-> Unifies sigma E1 /\ Unifies sigma E2.
Proof.
Admitted.

Instance equi_unifiable_app: Proper (equi_unifiable ++> equi_unifiable ++> equi_unifiable) (@List.app (eq X)).
Proof.
Admitted.

Lemma equi_unifiable_refl s: [(s, s)] ≈ nil.
Proof.
Admitted.

Lemma equi_unifiable_comm s t: [(s, t)] ≈ [(t, s)].
Proof.
Admitted.

Lemma equi_unifiable_decompose_app s1 s2 t1 t2: [(s1 s2, t1 t2)] ≈ [(s1, t1); (s2, t2)].
Proof.
Admitted.

Lemma equi_unifiable_cons x s E: (var x, s) :: E ≈ (var x, s) :: (update x s var •₊₊ E).
Proof.
intros ?; simplify; intuition idtac; cbn in *.
-
intros [u v] ?; mapinj; cbn; destruct x0 as [u' v'].
injection H2 as <- <-.
eapply H1 in H3; cbn in H3.
unfold unifies in *; cbn in *.
asimpl.
etransitivity; [ etransitivity; [| eapply H3] |].
all: eapply ext_exp; intros y; unfold funcomp, update; destruct eq_dec; subst; eauto.
-
intros [u v] ?; cbn.
unfold unifies in H0; cbn in H0.
eapply in_map with (f := subst_eq (update x s var)) in H.
eapply H1 in H; cbn in H; unfold unifies in H.
unfold unifies in *; cbn in *.
asimpl in H.
etransitivity; [ etransitivity; [| eapply H] |].
Admitted.

Lemma Vars_decomp' E E': decomp' E = Some E' -> Vars' E' ⊆ Vars' E.
Proof.
decomp_ind.
easy.
intros.
simplify.
now rewrite H1, vars_decomp; eauto.
