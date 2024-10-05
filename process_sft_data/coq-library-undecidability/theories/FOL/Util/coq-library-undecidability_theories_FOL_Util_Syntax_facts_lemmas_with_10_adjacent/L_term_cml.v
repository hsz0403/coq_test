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

Lemma find_bounded_t t : { n | bounded_t n t }.
Proof.
induction t using term_rect.
-
exists (S x).
constructor.
lia.
-
apply find_bounded_step in X as [n H].
exists n.
Admitted.

Lemma find_bounded {ff : falsity_flag} phi : { n | bounded n phi }.
Proof.
induction phi.
-
exists 0.
constructor.
-
destruct (find_bounded_step _ t) as [n Hn].
+
eauto using find_bounded_t.
+
exists n.
now constructor.
-
destruct IHphi1 as [n Hn], IHphi2 as [k Hk].
exists (n + k).
constructor; eapply bounded_up; try eassumption; lia.
-
destruct IHphi as [n Hn].
exists n.
constructor.
apply (bounded_up Hn).
Admitted.

Lemma find_bounded_L {ff : falsity_flag} A : { n | bounded_L n A }.
Proof.
induction A; cbn.
-
exists 0.
intros phi.
inversion 1.
-
destruct IHA as [k Hk], (find_bounded a) as [l Hl].
exists (k + l).
Admitted.

Lemma vec_cons_inv X n (v : Vector.t X n) x y : In y (Vector.cons X x n v) -> (y = x) \/ (In y v).
Proof.
inversion 1; subst.
-
now left.
-
apply EqDec.inj_right_pair in H3 as ->.
Admitted.

Lemma inj_pair2_eq_dec' A : eq_dec A -> forall (P : A -> Type) (p : A) (x y : P p), existT P p x = existT P p y -> x = y.
Proof.
Admitted.

Lemma dec_vec_in X n (v : vec X n) : (forall x, vec_in x v -> forall y, dec (x = y)) -> forall v', dec (v = v').
Proof with subst; try (now left + (right; intros[=])).
intros Hv.
induction v; intros v'; dependent elimination v'...
destruct (Hv h (vec_inB h v) h0)...
edestruct IHv.
-
intros x H.
apply Hv.
now right.
-
left.
f_equal.
apply e.
-
right.
intros H.
inversion H.
resolve_existT.
Admitted.

Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
intros v.
Admitted.

Instance dec_falsity : eq_dec falsity_flag.
Proof.
intros b b'.
unfold dec.
Admitted.

Lemma eq_dep_falsity b phi psi : eq_dep falsity_flag (@form Σ_funcs Σ_preds ops) b phi b psi <-> phi = psi.
Proof.
rewrite <- eq_sigT_iff_eq_dep.
split.
-
intros H.
resolve_existT.
reflexivity.
-
intros ->.
Admitted.

Lemma dec_form_dep {b1 b2} phi1 phi2 : dec (eq_dep falsity_flag (@form _ _ _) b1 phi1 b2 phi2).
Proof with subst; try (now left + (right; intros ? % eq_sigT_iff_eq_dep; resolve_existT; congruence)).
unfold dec.
revert phi2; induction phi1; intros; try destruct phi2.
all: try now right; inversion 1.
now left.
-
decide (b = b0)...
decide (P = P0)...
decide (t = t0)...
right.
intros [=] % eq_dep_falsity.
resolve_existT.
tauto.
-
decide (b = b1)...
decide (b0 = b2)...
destruct (IHphi1_1 phi2_1).
+
apply eq_dep_falsity in e as ->.
destruct (IHphi1_2 phi2_2).
*
apply eq_dep_falsity in e as ->.
now left.
*
right.
rewrite eq_dep_falsity in *.
intros [=].
now resolve_existT.
+
right.
rewrite eq_dep_falsity in *.
intros [=].
now repeat resolve_existT.
-
decide (b = b0)...
decide (q = q0)...
destruct (IHphi1 phi2).
+
apply eq_dep_falsity in e as ->.
now left.
+
right.
rewrite eq_dep_falsity in *.
intros [=].
Admitted.

Lemma list_prod_in X Y (x : X * Y) A B : x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
Proof.
induction A; cbn.
-
intros [].
-
intros [H | H] % in_app_or.
2: firstorder.
apply in_map_iff in H as (y & <- & Hel).
exists a, y.
Admitted.

Lemma vecs_from_correct X (A : list X) (n : nat) (v : vec X n) : (forall x, vec_in x v -> x el A) <-> v el vecs_from X A n.
Proof.
induction n; cbn.
-
split.
+
intros.
left.
now dependent elimination v.
+
intros [<- | []] x H.
inv H.
-
split.
+
intros.
dependent elimination v.
in_collect (pair h t0); destruct (IHn t0).
eauto using vec_inB.
apply H0.
intros x Hx.
apply H.
now right.
+
intros Hv.
apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
intros x H.
inv H; destruct (IHn v'); eauto.
apply H2; trivial.
Admitted.

Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) : cumulative L -> (forall x, vec_in x v -> exists m, x el L m) -> exists m, v el vecs_from _ (L m) n.
Proof.
intros HL Hv.
induction v; cbn.
-
exists 0.
tauto.
-
destruct IHv as [m H], (Hv h) as [m' H'].
1,3: eauto using vec_inB.
+
intros x Hx.
apply Hv.
now right.
+
exists (m + m').
in_collect (pair h v).
1: apply (cum_ge' (n:=m')); intuition lia.
apply vecs_from_correct.
rewrite <- vecs_from_correct in H.
intros x Hx.
apply (cum_ge' (n:=m)).
all: eauto.
Admitted.

Lemma enum_term : list_enumerator__T L_term term.
Proof with try (eapply cum_ge'; eauto; lia).
intros t.
induction t using term_rect.
-
exists (S x); cbn; eauto.
-
apply vec_forall_cml in H as [m H].
2: exact L_term_cml.
destruct (el_T F) as [m' H'].
exists (S (m + m')); cbn.
in_app 3.
eapply in_concat_iff.
eexists.
split.
2: in_collect F...
apply in_map.
rewrite <- vecs_from_correct in H |-*.
intros x H''.
Admitted.

Lemma enumT_term : enumerable__T term.
Proof.
apply enum_enumT.
exists L_term.
Admitted.

Lemma L_form_cml {ff : falsity_flag} : cumulative L_form.
Proof.
Admitted.

Lemma enum_form {ff : falsity_flag} : list_enumerator__T L_form form.
Proof with (try eapply cum_ge'; eauto; lia).
intros phi.
induction phi.
-
exists 1.
cbn; eauto.
-
rename t into v.
destruct (el_T P) as [m Hm], (vec_forall_cml term L_term _ v) as [m' Hm']; eauto using enum_term.
exists (S (m + m')); cbn.
in_app 2.
eapply in_concat_iff.
eexists.
split.
2: in_collect P...
eapply in_map.
rewrite <- vecs_from_correct in *.
intuition...
-
destruct (el_T b0) as [m Hm], IHphi1 as [m1], IHphi2 as [m2].
exists (1 + m + m1 + m2).
cbn.
in_app 3.
apply in_concat.
eexists.
split.
apply in_map...
in_collect (pair phi1 phi2)...
-
destruct (el_T q) as [m Hm], IHphi as [m' Hm'].
exists (1 + m + m').
cbn -[L_T].
in_app 4.
apply in_concat.
eexists.
split.
apply in_map...
Admitted.

Lemma enumT_form {ff : falsity_flag} : enumerable__T form.
Proof.
apply enum_enumT.
exists L_form.
Admitted.

Lemma L_term_cml : cumulative L_term.
Proof.
intros ?; cbn; eauto.
