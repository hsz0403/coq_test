Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski_facts.
Require Import Undecidability.FOL.ZF.
Require Import Lia.
From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Local Definition BSRS := list(card bool).
Fixpoint shift n x := match n with | O => x | S n => subst_term ↑ (shift n x) end.
Definition sing a := {a; a}.
Definition opair a b := {{a; a}; {a; b}}.
Definition pairing f A := ∀ $0 ∈ shift 1 f ~> ∃ ∃ $1 ∈ shift 3 A ∧ $2 ≡ opair $1 $0.
Definition function' f A := pairing f A ∧ ∀ ∃ $0 ∈ shift 2 A ∧ opair $0 $1 ∈ shift 2 f ∧ ∀ opair $1 $0 ∈ shift 2f ~> $2 ≡ $0.
Definition function f := ∀ ∀ ∀ opair $2 $1 ∈ shift 3 f ~> opair $2 $0 ∈ shift 3 f ~> $1 ≡ $0.
Definition enc_bool (x : bool) := if x then {∅; ∅} else ∅.
Fixpoint prep_string (s : string bool) a := match s with | nil => a | b::s => opair (enc_bool b) (prep_string s a) end.
Definition enc_string (s : string bool) := prep_string s ∅.
Fixpoint enc_stack (B : BSRS) := match B with | nil => ∅ | (s,t)::B => enc_stack B ∪ sing (opair (enc_string s) (enc_string t)) end.
Definition is_rep phi a b := ∀ $0 ∈ shift 1 b <~> ∃ $0 ∈ shift 2 a ∧ phi.
Definition comb_rel s t := ∃ ∃ $2 ≡ opair $0 $1 ∧ $3 ≡ opair (prep_string s $0) (prep_string t $1).
Fixpoint combinations (B : BSRS) a b := match B with | nil => b ≡ ∅ | (s,t)::B => ∃ ∃ shift 2 b ≡ $0 ∪ $1 ∧ combinations B (shift 2 a) $1 ∧ is_rep (comb_rel s t) (shift 2 a) $0 end.
Definition solutions (B : BSRS) f n := opair ∅ (enc_stack B) ∈ f ∧ ∀ ∀ ∀ $2 ∈ shift 3 n ~> opair $2 $1 ∈ shift 3 f ~> combinations B $1 $0 ~> opair (σ $2) $0 ∈ shift 3 f.
Definition solvable (B : BSRS) := ∃ ∃ ∃ ∃ $3 ∈ ω ∧ function $2 ∧ solutions B $2 $3 ∧ opair $3 $0 ∈ $2 ∧ opair $1 $1 ∈ $0.
Declare Scope sem.
Open Scope sem.
Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.
Notation "x ∈ y" := (@i_atom _ _ _ _ elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : sem.
Notation "x ≡ y" := (@i_atom _ _ _ _ equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : sem.
Notation "x ⊆ y" := (forall z, z ∈ x -> z ∈ y) (at level 34) : sem.
Notation "∅" := (@i_func ZF_func_sig ZF_pred_sig _ _ eset Vector.nil) : sem.
Notation "'ω'" := (@i_func ZF_func_sig _ _ _ om Vector.nil) : sem.
Notation "{ x ; y }" := (@i_func ZF_func_sig _ _ _ pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 31) : sem.
Notation "⋃ x" := (@i_func ZF_func_sig _ _ _ union (Vector.cons x Vector.nil)) (at level 32) : sem.
Notation "'PP' x" := (@i_func ZF_func_sig _ _ _ power (Vector.cons x Vector.nil)) (at level 31) : sem.
Notation "x ∪ y" := (⋃ {x; y}) (at level 32) : sem.
Notation "'σ' x" := (x ∪ {x; x}) (at level 32) : sem.
Section ZF.
Context { V : Type }.
Context { M : interp V }.
Hypothesis M_ZF : forall rho, rho ⊫ ZF'.
Hypothesis VIEQ : extensional M.
Definition M_inductive x := ∅ ∈ x /\ forall y, y ∈ x -> σ y ∈ x.
Definition agrees_fun phi (P : V -> Prop) := forall x rho, P x <-> (x.:rho) ⊨ phi.
Definition def_pred (P : V -> Prop) := exists phi rho, forall d, P d <-> (d.:rho) ⊨ phi.
Definition M_is_rep R x y := forall v, v ∈ y <-> exists u, u ∈ x /\ R u v.
Definition functional (R : V -> V -> Prop) := forall x y y', R x y -> R x y' -> y = y'.
Definition def_rel (R : V -> V -> Prop) := exists phi rho, forall x y, R x y <-> (x.:y.:rho) ⊨ phi.
Definition M_sing x := {x; x}.
Definition M_opair x y := ({{x; x}; {x; y}}).
Hint Resolve binunionl binunionr : core.
Fixpoint numeral n := match n with | O => ∅ | S n => σ (numeral n) end.
Definition trans x := forall y, y ∈ x -> y ⊆ x.
Definition M_enc_bool (x : bool) := if x then {∅; ∅} else ∅.
Fixpoint M_prep_string (s : string bool) x := match s with | nil => x | b::s => M_opair (M_enc_bool b) (M_prep_string s x) end.
Definition M_enc_string (s : string bool) := M_prep_string s ∅.
Definition M_enc_card s t := M_opair (M_enc_string s) (M_enc_string t).
Fixpoint M_enc_stack (B : BSRS) := match B with | nil => ∅ | (s,t)::B => M_enc_stack B ∪ M_sing (M_enc_card s t) end.
Definition append_all A (c : card bool) := map (fun p => (fst c ++ fst p, snd c ++ snd p)) A.
Definition derivation_step B C := flat_map (append_all C) B.
Fixpoint derivations B n := match n with | O => B | S n => derivation_step B (derivations B n) end.
Fixpoint M_enc_derivations B n := match n with | O => M_sing (M_opair ∅ (M_enc_stack B)) | S n => M_enc_derivations B n ∪ M_sing (M_opair (numeral (S n)) (M_enc_stack (derivations B (S n)))) end.
Definition M_comb_rel s t := fun u v => exists u1 u2, u = M_opair u1 u2 /\ v = M_opair (M_prep_string s u1) (M_prep_string t u2).
Fixpoint M_combinations B x y := match B with | nil => y = ∅ | (s,t)::B => exists y1 y2, y = y2 ∪ y1 /\ M_combinations B x y1 /\ M_is_rep (M_comb_rel s t) x y2 end.
Definition M_solutions B f n := M_opair ∅ (M_enc_stack B) ∈ f /\ forall k x y, k ∈ n -> M_opair k x ∈ f -> M_combinations B x y -> M_opair (σ k) y ∈ f.
Definition M_function f := forall x y y', M_opair x y ∈ f -> M_opair x y' ∈ f -> y = y'.
Definition standard := forall x, x ∈ ω -> exists n, x ≡ numeral n.
End ZF.
Arguments standard {_} _.

Lemma pair_com x y : {x; y} = {y; x}.
Proof.
Admitted.

Lemma binunion_com x y : x ∪ y = y ∪ x.
Proof.
Admitted.

Lemma binunionl a x y : a ∈ x -> a ∈ x ∪ y.
Proof.
intros H.
apply binunion_el.
Admitted.

Lemma binunionr a x y : a ∈ y -> a ∈ x ∪ y.
Proof.
intros H.
apply binunion_el.
Admitted.

Lemma binunion_assoc x y z : (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
apply M_ext; intros a [H|H] % binunion_el; eauto.
-
apply binunion_el in H as [H|H]; eauto.
-
Admitted.

Lemma numeral_omega n : numeral n ∈ ω.
Proof.
Admitted.

Lemma numeral_trans n : trans (numeral n).
Proof.
induction n; cbn.
-
intros x H.
now apply M_eset in H.
-
intros x [H| ->] % sigma_el; try apply sigma_sub.
apply IHn in H.
Admitted.

Lemma numeral_wf n : ~ numeral n ∈ numeral n.
Proof.
induction n.
-
apply M_eset.
-
intros [H|H] % sigma_el; fold numeral in *.
+
apply IHn.
eapply numeral_trans; eauto.
apply sigma_eq.
+
assert (numeral n ∈ numeral (S n)) by apply sigma_eq.
Admitted.

Lemma numeral_lt k l : k < l -> numeral k ∈ numeral l.
Proof.
Admitted.

Lemma numeral_inj k l : numeral k = numeral l -> k = l.
Proof.
intros Hk.
assert (k = l \/ k < l \/ l < k) as [H|[H|H]] by lia; trivial.
Admitted.

Lemma enc_string_inj s t : M_enc_string s = M_enc_string t -> s = t.
Proof.
induction s in t|-*; destruct t as [|b t]; cbn; trivial.
-
intros H.
contradiction (M_eset (x:=M_sing (M_enc_bool b))).
rewrite H.
apply M_pair.
now left.
-
intros H.
contradiction (M_eset (x:=M_sing (M_enc_bool a))).
rewrite <- H.
apply M_pair.
now left.
-
intros [H1 H2] % opair_inj.
apply IHs in H2 as ->.
apply enc_bool_inj in H1 as ->.
Admitted.

Lemma eval_opair rho x y : eval rho (opair x y) = M_opair (eval rho x) (eval rho y).
Proof.
Admitted.

Lemma eval_enc_bool rho b : eval rho (enc_bool b) = M_enc_bool b.
Proof.
Admitted.

Lemma eval_prep_string rho s x : eval rho (prep_string s x) = M_prep_string s (eval rho x).
Proof.
induction s; trivial.
cbn [prep_string].
Admitted.

Lemma eval_enc_string rho s : eval rho (enc_string s) = M_enc_string s.
Proof.
unfold enc_string.
Admitted.

Lemma eval_enc_stack rho B : eval rho (enc_stack B) = M_enc_stack B.
Proof.
induction B; cbn; trivial.
destruct a.
unfold M_enc_card.
Admitted.

Lemma M_enc_stack_app A B : M_enc_stack (A ++ B) = M_enc_stack A ∪ M_enc_stack B.
Proof.
induction A as [|[s t] A IH]; cbn.
-
apply binunion_eset.
-
rewrite IH.
rewrite !binunion_assoc.
Admitted.

Lemma enc_stack_el' x A : x ∈ M_enc_stack A -> exists s t, (s, t) el A /\ x = M_enc_card s t.
Proof.
induction A as [|[s t] A IH]; cbn.
-
now intros H % M_eset.
-
intros [H|H] % binunion_el.
+
destruct (IH H) as (u&v&H'&->).
exists u, v.
intuition.
+
apply sing_el in H as ->.
exists s, t.
Admitted.

Lemma enc_stack_el B s t : (s, t) el B -> M_enc_card s t ∈ M_enc_stack B.
Proof.
induction B as [|[u b] B IH]; cbn; auto.
intros [H|H]; apply binunion_el.
-
right.
apply sing_el.
congruence.
-
left.
Admitted.

Lemma M_prep_enc s s' : M_prep_string s (M_enc_string s') = M_enc_string (s ++ s').
Proof.
induction s; cbn; trivial.
Admitted.

Lemma enc_bool_inj b c : M_enc_bool b = M_enc_bool c -> b = c.
Proof.
destruct b, c; trivial; cbn.
-
intros H.
contradiction (@M_eset ∅).
pattern ∅ at 2.
rewrite <- H.
apply M_pair; auto.
-
intros H.
contradiction (@M_eset ∅).
pattern ∅ at 2.
rewrite H.
apply M_pair; auto.
