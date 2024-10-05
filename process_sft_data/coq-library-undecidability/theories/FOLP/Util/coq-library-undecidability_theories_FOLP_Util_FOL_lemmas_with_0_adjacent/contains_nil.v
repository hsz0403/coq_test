Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Equations.Equations Equations.Prop.DepElim Arith Undecidability.Shared.Libs.PSL.Numbers List Setoid.
From Undecidability.Synthetic Require Export DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.FOLP Require Export Syntax.
Require Export Lia.
Notation "phi --> psi" := (Impl phi psi) (right associativity, at level 55).
Notation "∀ phi" := (All phi) (at level 56, right associativity).
Notation "⊥" := (Fal).
Notation "¬ phi" := (phi --> ⊥) (at level 20).
Notation "phi ∨ psi" := (¬ phi --> psi) (left associativity, at level 54).
Notation "phi ∧ psi" := (¬ (¬ phi ∨ ¬ psi)) (left associativity, at level 54).
Notation "∃ phi" := (¬ ∀ ¬ phi) (at level 56, right associativity).
Notation vector := Vector.t.
Import Vector.
Arguments nil {A}.
Arguments cons {A} _ {n}.
Derive Signature for vector.
Ltac capply H := eapply H; try eassumption.
Ltac comp := repeat (progress (cbn in *; autounfold in *; asimpl in *)).
Hint Unfold idsRen : core.
Ltac resolve_existT := match goal with | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => rewrite (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2) in * | _ => idtac end.
Ltac inv H := inversion H; subst; repeat (progress resolve_existT).
Section FOL.
Context {Sigma : Signature}.
Inductive sf : form -> form -> Prop := | SImplL phi psi : sf phi (phi --> psi) | SImplR phi psi : sf psi (phi --> psi) | SAll phi t : sf (phi [t .: ids]) (∀ phi).
Hint Constructors sf : core.
Fixpoint size (phi : form ) := match phi with | Pred _ _ => 0 | Fal => 0 | Impl phi psi => S (size phi + size psi) | All phi => S (size phi) end.
Inductive Forall (A : Type) (P : A -> Type) : forall n, vector A n -> Type := | Forall_nil : Forall P (@Vector.nil A) | Forall_cons : forall n (x : A) (l : vector A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).
Inductive vec_in (A : Type) (a : A) : forall n, vector A n -> Type := | vec_inB n (v : vector A n) : vec_in a (cons a v) | vec_inS a' n (v :vector A n) : vec_in a v -> vec_in a (cons a' v).
Hint Constructors vec_in : core.
Inductive unused_term (n : nat) : term -> Prop := | uft_var m : n <> m -> unused_term n (var_term m) | uft_Func F v : (forall t, vec_in t v -> unused_term n t) -> unused_term n (Func F v).
Inductive unused (n : nat) : form -> Prop := | uf_Fal : unused n Fal | uf_Pred P v : (forall t, vec_in t v -> unused_term n t) -> unused n (Pred P v) | uf_Impl phi psi : unused n phi -> unused n psi -> unused n (Impl phi psi) | uf_All phi : unused (S n) phi -> unused n (All phi).
Definition unused_L n A := forall phi, List.In phi A -> unused n phi.
Definition closed phi := forall n, unused n phi.
Definition capture n phi := nat_rect _ phi (fun _ => All) n.
Definition close phi := capture (proj1_sig (find_unused phi)) phi.
Fixpoint big_imp A phi := match A with | List.nil => phi | a :: A' => a --> (big_imp A' phi) end.
Definition shift_P P n := match n with | O => False | S n' => P n' end.
Definition theory := form -> Prop.
Definition contains phi (T : theory) := T phi.
Definition contains_L (A : list form) (T : theory) := forall f, List.In f A -> contains f T.
Definition subset_T (T1 T2 : theory) := forall (phi : form), contains phi T1 -> contains phi T2.
Definition list_T A : theory := fun phi => List.In phi A.
Infix "⊏" := contains_L (at level 20).
Infix "⊑" := subset_T (at level 20).
Infix "∈" := contains (at level 70).
Hint Unfold contains : core.
Hint Unfold contains_L : core.
Hint Unfold subset_T : core.
Global Instance subset_T_trans : Transitive subset_T.
Proof.
intros T1 T2 T3.
intuition.
Definition extend T (phi : form) := fun psi => T psi \/ psi = phi.
Infix "⋄" := extend (at level 20).
Definition closed_T (T : theory) := forall phi n, contains phi T -> unused n phi.
Section ContainsAutomation.
End ContainsAutomation.
End FOL.
Definition tmap {S1 S2 : Signature} (f : @form S1 -> @form S2) (T : @theory S1) : @theory S2 := fun phi => exists psi, T psi /\ f psi = phi.
Hint Constructors vec_in : core.
Infix "⊏" := contains_L (at level 20).
Infix "⊑" := subset_T (at level 20).
Infix "∈" := contains (at level 70).
Infix "⋄" := extend (at level 20).
Hint Resolve contains_nil contains_cons contains_cons2 contains_app : contains_theory.
Hint Resolve contains_extend1 contains_extend2 contains_extend3 : contains_theory.
Ltac use_theory A := exists A; split; [eauto 15 with contains_theory|].
Fixpoint vecs_from X (A : list X) (n : nat) : list (vector X n) := match n with | 0 => [Vector.nil] | S n => [ cons x v | (x, v) ∈ (A × vecs_from A n) ] end.
Fixpoint L_vec X (L : nat -> list X) n m : list (vector X n) := match m with | 0 => [] | S m => L_vec L n m ++ vecs_from (cumul L m) n end.
Instance enumT_vec X L_T {HX : list_enumerator__T L_T X} n : list_enumerator__T (L_vec L_T n) (vector X n).
Proof with try (eapply cum_ge'; eauto; lia).
intros v.
enough (exists m, forall x, vec_in x v -> x el cumul L_T m) as [m Hm].
{
exists (S m).
cbn.
in_app 2.
now rewrite <- vecs_from_correct.
}
induction v.
+
exists 0.
intros x H.
inv H.
+
destruct (cumul_spec__T HX h) as [m Hm], IHv as [m' Hm'].
exists (m + m').
intros x Hx.
inv Hx...
Defined.
Section Enumerability.
Context {Sigma : Signature}.
Variable e_F : nat -> list Funcs.
Variable e_P : nat -> list Preds.
Hypothesis enum_Funcs : list_enumerator__T e_F Funcs.
Hypothesis enum_Preds : list_enumerator__T e_P Preds.
Fixpoint L_term n : list term := match n with | 0 => [] | S n => L_term n ++ var_term n :: concat ([ [ Func F v | v ∈ vecs_from (L_term n) (fun_ar F) ] | F ∈ L_T n]) end.
Global Instance enumT_term : list_enumerator__T L_term term.
Proof with try (eapply cum_ge'; eauto; lia).
intros t.
induction t using strong_term_ind.
+
exists (S x); cbn.
now in_app 2.
+
apply vec_forall_cml in H as [m H].
2: exact L_term_cml.
destruct (cumul_spec__T enum_Funcs F) as [m' H'].
exists (S (m + m')); cbn.
in_app 3.
eapply in_concat_iff.
eexists.
split.
2: in_collect F...
apply in_map.
rewrite <- vecs_from_correct in H |-*.
intros x H''.
specialize (H x H'')...
Defined.
Fixpoint L_form n : list form := match n with | 0 => [Fal] | S n => L_form n ++ [Fal] ++ concat ([ [ Pred P v | v ∈ L_T (H := @enumT_vec _ _ _ _) n ] | P ∈ L_T n]) ++ [ phi1 --> phi2 | (phi1, phi2) ∈ (L_form n × L_form n) ] ++ [ ∀ phi | phi ∈ L_form n ] end.
Global Instance enumT_form : list_enumerator__T L_form form.
Proof with (try eapply cum_ge'; eauto; lia).
intros phi.
induction phi.
+
exists 1.
cbn; eauto.
+
destruct (el_T P) as [m Hm], (el_T t) as [m' Hm'].
exists (S (m + m')); cbn.
in_app 3.
eapply in_concat_iff.
eexists.
split.
2: in_collect P...
apply in_map...
+
destruct IHphi1 as [m1], IHphi2 as [m2].
exists (1 + m1 + m2).
cbn.
in_app 4.
in_collect (pair phi1 phi2)...
+
destruct IHphi as [m].
exists (S m).
cbn -[L_T].
in_app 5.
in_collect phi...
Defined.
End Enumerability.
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vector X n).
Proof.
intros v.
refine (dec_vec_in _).
Section EqDec.
Context {Sigma : Signature}.
Hypothesis eq_dec_Funcs : eq_dec Funcs.
Hypothesis eq_dec_Preds : eq_dec Preds.
Global Instance dec_term : eq_dec term.
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
intros t.
induction t using strong_term_ind; intros []...
-
decide (x = n)...
-
decide (F = f)...
destruct (dec_vec_in X t)...
Global Instance dec_form : eq_dec form.
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
intros phi.
induction phi; intros []...
-
decide (P = P0)...
decide (t = t0)...
-
decide (phi1 = f)...
decide (phi2 = f0)...
-
decide (phi = f)...
End EqDec.
Section Subterm.
Context {Sigma : Signature}.
Definition form_shift n := var_term (S n).
Notation "↑" := form_shift.
Inductive subterm t : term -> Prop := | stB : subterm t t | stF F v s : vec_in s v -> subterm t s -> subterm t (Func F v).
Inductive subterm_form t : form -> Prop := | stP P v s : vec_in s v -> subterm t s -> subterm_form t (Pred P v) | stIL phi psi : subterm_form t phi -> subterm_form t (phi --> psi) | stIR phi psi : subterm_form t psi -> subterm_form t (phi --> psi) | stA phi : subterm_form t[↑] phi -> subterm_form t (∀ phi).
End Subterm.
Section SigExt.
Hint Unfold axioms.funcomp : core.
Definition sig_ext (Sigma : Signature) : Signature := match Sigma with B_S Funcs fun_ar Preds pred_ar => B_S (Funcs + nat) (fun f => match f with inl f' => fun_ar f' | inr _ => 0 end) Preds pred_ar end.
Global Instance dec_sig_ext_Funcs {Sigma : Signature} (H : eq_dec Funcs) : eq_dec (@Funcs (sig_ext Sigma)).
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
destruct Sigma.
intros [] []...
-
decide (f = f0)...
-
decide (n = n0)...
Global Instance dec_sig_ext_Preds {Sigma : Signature} (H : eq_dec Preds) : eq_dec (@Preds (sig_ext Sigma)).
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
destruct Sigma.
exact H.
Global Instance enumT_sig_ext_Funcs {Sigma : Signature} {f} {H : list_enumerator__T f Funcs} : inf_list_enumerable__T (@Funcs (sig_ext Sigma)).
Proof with (try eapply cum_ge'; eauto; lia).
destruct Sigma.
exists (fix f n := match n with 0 => List.map inl (L_T 0) | S n' => f n' ++ (inr n') :: List.map inl (L_T n') end).
1: eauto.
intros [f0|].
2: exists (S n); in_app 2...
destruct (el_T f0) as [m Hin].
exists (S m).
in_app 3.
in_collect f0...
Global Instance enumT_sig_ext_Preds {Sigma : Signature} {f} {H : list_enumerator__T f Preds} : inf_list_enumerable__T (@Preds (sig_ext Sigma)).
Proof.
destruct Sigma.
eexists.
exact H.
Fixpoint sig_lift_term' F F_ar P P_ar (t : @term (B_S F F_ar P P_ar)) : (@term (sig_ext (B_S F F_ar P P_ar))) := match t with | var_term x => var_term x | Func f v => @Func (sig_ext (B_S F F_ar P P_ar)) (inl f) (map (fun x => sig_lift_term' x) v) end.
Definition sig_lift_term {Sigma : Signature} : @term Sigma -> @term (sig_ext Sigma) := match Sigma return @term Sigma -> @term (sig_ext Sigma) with B_S Funcs fun_ar Preds pred_ar as S => fun t => sig_lift_term' t end.
Hint Unfold sig_lift_term : core.
Fixpoint sig_lift' F F_ar P P_ar (phi : @form (B_S F F_ar P P_ar)) : (@form (sig_ext (B_S F F_ar P P_ar))) := match phi with | Fal => Fal | Pred p v => @Pred (sig_ext (B_S F F_ar P P_ar)) p (map sig_lift_term v) | Impl phi psi => Impl (sig_lift' phi) (sig_lift' psi) | All phi => All (sig_lift' phi) end.
Definition sig_lift {Sigma : Signature} : @form Sigma -> @form (sig_ext Sigma) := match Sigma return @form Sigma -> @form (sig_ext Sigma) with B_S Funcs fun_ar Preds pred_ar as Sig => fun phi => sig_lift' phi end.
Hint Unfold sig_lift : core.
Fixpoint fin_minus (n m : nat) : (n < m) + {x | x = n - m} := match n, m with | n', 0 => inr (exist (fun x => x = n' - 0) n' eq_refl) | 0, S m' => inl (le_n_S 0 m' (Nat.le_0_l m')) | S n', S m' => match fin_minus n' m' with | inr (exist _ x H) => inr (exist _ x H) | inl H => inl (le_n_S (S n') m' H) end end.
Definition vsubs {Sigma : Signature} (n m : nat) (v : vector term n) (x : nat) : term := match fin_minus x n with | inl i => nth_order v i | inr (exist _ y _) => var_term (y + m) end.
Hint Unfold vsubs : core.
Fixpoint sig_drop_term' F F_ar P P_ar (n : nat) (t : @term (sig_ext (B_S F F_ar P P_ar))) : @term (B_S F F_ar P P_ar) := match t with | var_term x => var_term x | Func (inl f') v => @Func (B_S F F_ar P P_ar) f' (map (fun x => sig_drop_term' n x) v) | Func (inr y) _ => var_term (n + y) end.
Definition sig_drop_term {Sigma : Signature} (n : nat) : @term (sig_ext Sigma) -> @term Sigma := match Sigma return @term (sig_ext Sigma) -> @term Sigma with B_S Funcs fun_ar Preds pred_ar as S => sig_drop_term' n end.
Hint Unfold sig_drop_term : core.
Fixpoint sig_drop' F F_ar P P_ar (n : nat) (phi : @form (sig_ext (B_S F F_ar P P_ar))) : @form (B_S F F_ar P P_ar) := match phi with | Fal => Fal | Pred p v => @Pred (B_S F F_ar P P_ar) p (map (sig_drop_term n) v) | Impl phi psi => Impl (sig_drop' n phi) (sig_drop' n psi) | All phi => All (sig_drop' (S n) phi) end.
Definition sig_drop {Sigma : Signature} (n : nat) : @form (sig_ext Sigma) -> @form Sigma := match Sigma return @form (sig_ext Sigma) -> @form Sigma with B_S Funcs fun_ar Preds pred_ar as Sig => sig_drop' n end.
Hint Unfold sig_drop : core.
Definition ext_c' f f_ar P P_ar (n : nat) : term := @Func (sig_ext (B_S f f_ar P P_ar)) (inr n) Vector.nil.
Definition ext_c {Sigma : Signature} (n : nat) : @term (sig_ext Sigma) := match Sigma with B_S f f_ar P P_ar => ext_c' f_ar P_ar n end.
Definition pref {Sigma : Signature} (n : nat) (rho : nat -> term) (x : nat) : term := match fin_minus x n with | inl i => var_term x | inr (exist _ y _) => rho y end.
Definition raise {Sigma : Signature} (n : nat) (x : nat) : term := var_term (n + x).
Hint Unfold ext_c' pref raise : core.
End SigExt.
Notation "↑" := form_shift.
Notation "A ⟹ phi" := (big_imp A phi) (at level 60, right associativity).

Lemma contains_nil T : List.nil ⊏ T.
Proof.
firstorder.
