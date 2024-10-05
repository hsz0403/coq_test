Set Implicit Arguments.
Require Import List Arith Lia Morphisms FinFun.
Import ListNotations.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics equivalence typing order.
Set Default Proof Using "Type".
Notation "sigma •₊ A" := (map (subst_exp sigma) A) (at level 69).
Notation renL delta A := (map (ren delta) A).
Notation Vars := (flat_map vars).
Section TermsExtension.
Context {X: Const}.
Implicit Types (s t: exp X) (n m: nat) (Gamma Delta: ctx) (A B: type) (sigma tau: fin -> exp X) (delta xi: fin -> fin) (S T: list (exp X)) (L: list type).
Reserved Notation "Gamma ⊢₊ A : L" (at level 80, A at level 99).
Inductive listtyping Gamma : list (exp X) -> list type -> Prop := | listtyping_nil: Gamma ⊢₊ nil : nil | listtyping_cons s S A L: Gamma ⊢ s : A -> Gamma ⊢₊ S : L -> Gamma ⊢₊ s :: S : A :: L where "Gamma ⊢₊ A : L" := (listtyping Gamma A L).
Hint Constructors listtyping : core.
Reserved Notation "Gamma ⊢₊( n ) A : L" (at level 80, A at level 99).
Inductive orderlisttyping n Gamma: list (exp X) -> list type -> Prop := | orderlisttyping_nil: Gamma ⊢₊(n) nil : nil | orderlisttyping_cons s S A L: Gamma ⊢(n) s : A -> Gamma ⊢₊(n) S : L -> Gamma ⊢₊(n) s :: S : A :: L where "Gamma ⊢₊( n ) A : L" := (orderlisttyping n Gamma A L).
Hint Constructors orderlisttyping : core.
Section ListTypingProperties.
End ListTypingProperties.
Notation "S >₊ T" := (lstep step S T) (at level 60).
Notation "S >₊* T" := (star (lstep step) S T) (at level 60).
Notation "S ≡₊ T" := (equiv (lstep step) S T) (at level 60).
Section ListSemanticProperties.
Global Instance list_ren_proper delta: Proper (equiv (lstep step) ++> equiv (lstep (@step X))) (map (ren delta)).
Proof.
intros ??; now eapply list_equiv_ren.
Global Instance list_subst_proper sigma: Proper (equiv (lstep step) ++> equiv (lstep (@step X))) (map (subst_exp sigma)).
Proof.
intros ??; now eapply list_equiv_subst.
End ListSemanticProperties.
Section ArrowProperties.
Fixpoint Arr (B: list type) (A: type) := match B with | nil => A | A' :: B => A' → (Arr B A) end.
End ArrowProperties.
Hint Rewrite ord'_app ord_Arr ord_repeated : simplify.
Hint Rewrite ord_Arr target_Arr target_ord : simplify.
Fixpoint Lambda (n: nat) (s: exp X) := match n with | 0 => s | S n => lambda (Lambda n s) end.
Fixpoint AppR (e: exp X) (A: list (exp X)) := match A with | nil => e | e' :: A => AppR e A e' end.
Fixpoint AppL (A: list (exp X)) (e: exp X) := match A with | nil => e | e' :: A => e' (AppL A e) end.
Hint Rewrite AppR_head : simplify.
Section ListOperatorsSubstitutionRenaming.
End ListOperatorsSubstitutionRenaming.
Section ListOperatorsCompatibilityProperties.
Global Instance Lambda_step_proper k: Proper (step ++> step) (Lambda k).
Proof.
induction k; cbn; intros ??; (eauto 3).
Global Instance AppR_step_proper: Proper (step ++> eq ++> step) AppR.
Proof.
intros s t ? ? A ->.
induction A in s, t, H |-*; cbn; (eauto 3).
Global Instance AppR_lstep_proper: Proper (eq ++> lstep step ++> step) AppR.
Proof.
intros ? ? -> ? ? H.
induction H in y |-*; cbn; (eauto 2).
Global Instance AppL_step_proper: Proper (eq ++> step ++> step) AppL.
Proof.
intros ? A -> s t H.
induction A in s, t, H |-*; cbn; (eauto 3).
Global Instance AppL_lstep_proper: Proper (lstep step ++> eq ++> step) AppL.
Proof.
intros ? ? H ? t ->.
induction H in t |-*; cbn; (eauto 2).
Global Instance Lambda_steps_proper k: Proper (star step ++> star step) (Lambda k).
Proof.
induction 1; (eauto 1); now rewrite H.
Global Instance AppL_proper: Proper (star (lstep step) ++> star step ++> star step) AppL.
Proof.
intros ? ?.
induction 1.
-
intros ? ? ?.
induction H; cbn; (eauto 2).
rewrite <-IHstar.
econstructor 2; (eauto 1); eapply AppL_step_proper; (eauto 2).
-
intros ? ? ?.
rewrite H.
specialize (IHstar _ _ H1).
now rewrite IHstar.
Global Instance AppR_proper: Proper (star step ++> star (lstep step) ++> star step) AppR.
Proof.
intros ? ?.
induction 1.
-
intros ? ? ?.
induction H; cbn; (eauto 2).
rewrite <-IHstar.
econstructor 2; (eauto 1); eapply AppR_lstep_proper; (eauto 2).
-
intros ? ? ?.
rewrite H.
specialize (IHstar _ _ H1).
now rewrite IHstar.
Global Instance Lambda_equiv_proper n: Proper (equiv step ++> equiv step) (Lambda n).
Proof.
intros ? ? ?; induction n; cbn; (eauto 2).
now rewrite IHn.
Global Instance equiv_AppL_proper: Proper (equiv (lstep step) ++> equiv step ++> equiv step) AppL.
Proof.
intros ? ? (? & H1 & H2) % church_rosser ? ? (? & H3 & H4) % church_rosser; eauto.
now rewrite H1, H2, H3, H4.
Global Instance equiv_AppR_proper: Proper (equiv step ++> equiv (lstep step) ++> equiv step) AppR.
Proof.
intros ? ? (? & H1 & H2) % church_rosser ? ? (? & H3 & H4) % church_rosser; (eauto 2).
now rewrite H1, H2, H3, H4.
End ListOperatorsCompatibilityProperties.
Section EquivalenceInversions.
End EquivalenceInversions.
Section Normality.
End Normality.
Hint Resolve normal_Lambda normal_AppR_left normal_AppR_right : core.
Section ListOperatorsTyping.
End ListOperatorsTyping.
Section Utilities.
Inductive nf: exp X -> Type := nfc k s t T: (forall t, t ∈ T -> nf t) -> isAtom s -> t = Lambda k (AppR s T) -> nf t.
End Utilities.
End TermsExtension.
Hint Constructors listtyping : core.
Hint Constructors orderlisttyping : core.
Hint Rewrite ord'_app ord_Arr ord_repeated : simplify.
Hint Rewrite ord_Arr : simplify.
Hint Resolve normal_Lambda normal_AppR_left normal_AppR_right : core.
Hint Rewrite @Lambda_ren @Lambda_subst @AppL_ren @AppL_subst @AppR_ren @AppR_subst : asimpl.
Hint Rewrite @AppR_head : simplify.
Hint Rewrite target_Arr target_ord: simplify.
Hint Rewrite arity_Arr : simplify.
Notation "S >₊ T" := (lstep step S T) (at level 60).
Notation "S >₊* T" := (star (lstep step) S T) (at level 60).
Notation "S ≡₊ T" := (equiv (lstep step) S T) (at level 60).
Notation "Gamma ⊢₊ A : L" := (listtyping Gamma A L) (at level 80, A at level 99).
Notation "Gamma ⊢₊( n ) A : L" := (orderlisttyping n Gamma A L) (at level 80, A at level 99).

Lemma Arr_inversion L1 L2 A1 A2: length L1 <= length L2 -> Arr L1 A1 = Arr L2 A2 -> exists L, L2 = L1 ++ L /\ A1 = Arr L A2.
Proof.
induction L1 in L2, A1, A2 |-*; cbn.
-
intros _.
exists L2.
intuition.
-
destruct L2.
inversion 1.
intros H H1.
cbn in H.
eapply le_S_n in H.
injection H1 as ??.
subst.
edestruct IHL1; (eauto 2).
intuition.
exists x; intuition.
Admitted.

Lemma type_decompose: forall A, exists L beta, A = Arr L (typevar beta).
Proof.
induction A; cbn.
-
exists nil; exists n.
reflexivity.
-
destruct IHA2 as (L & beta & H).
subst.
exists (A1 :: L); exists beta.
Admitted.

Lemma target_ord A: ord (target A) = 1.
Proof.
Admitted.

Lemma arity_decomposed L beta: arity (Arr L (typevar beta)) = length L.
Proof.
Admitted.

Lemma Arr_left_injective L1 L2 A: Arr L1 A = Arr L2 A -> L1 = L2.
Proof.
destruct (le_ge_dec (length L1) (length L2)); intros H; [|symmetry in H].
all: eapply Arr_inversion in H as [L3]; (eauto 1); intuition.
all: destruct L3; simplify in *; (eauto 2).
all: eapply (f_equal arity) in H1; cbn in H1; rewrite arity_Arr in H1.
Admitted.

Lemma ord_Arr L A: ord (Arr L A) = max (1 + ord' L) (ord A).
Proof.
induction L; cbn -[max].
symmetry; eapply Nat.max_r.
eapply ord_1.
rewrite IHL, Nat.max_assoc.
cbn [plus].
Admitted.

Lemma target_Arr L A: target (Arr L A) = target A.
Proof.
Admitted.

Lemma ord_repeated n A: ord' (repeat A n) <= ord A.
Proof.
induction n; cbn; (eauto 2).
Admitted.

Lemma Lambda_plus (n m: nat) s: Lambda n (Lambda m s) = Lambda (n + m) s.
Proof.
Admitted.

Lemma Lambda_injective n (s t: exp X): Lambda n s = Lambda n t -> s = t.
Proof.
Admitted.

Lemma AppR_app T1 T2 s: AppR s (T1 ++ T2) = AppR (AppR s T2) T1.
Proof.
Admitted.

Lemma AppR_vars s T: vars (AppR s T) === vars s ++ Vars T.
Proof.
induction T; cbn; simplify; lauto.
rewrite IHT, <-app_assoc; eapply proper_app_seteq; lauto.
Admitted.

Lemma AppR_head s T: head (AppR s T) = head s.
Proof.
Admitted.

Lemma Lambda_ren delta n s: ren delta (Lambda n s) = Lambda n (ren (it n up_ren delta) s).
Proof.
induction n in delta |-*; cbn; (eauto 2).
rewrite IHn.
do 3 f_equal.
symmetry.
Admitted.

Lemma Lambda_subst sigma n s: sigma • (Lambda n s) = Lambda n (it n up sigma • s).
Proof.
induction n in sigma |-*; cbn; (eauto 2).
rewrite IHn; do 3 f_equal.
symmetry.
Admitted.

Lemma AppL_ren delta S t: ren delta (AppL S t) = AppL (renL delta S) (ren delta t).
Proof.
Admitted.

Lemma AppL_subst sigma S t: sigma • AppL S t = AppL (sigma •₊ S) (sigma • t).
Proof.
Admitted.

Lemma AppR_ren delta s T: ren delta (AppR s T) = AppR (ren delta s) (renL delta T) .
Proof.
Admitted.

Lemma AppR_subst sigma s T: sigma • AppR s T = AppR (sigma • s) (sigma •₊ T).
Proof.
Admitted.

Lemma AppR_Lambda T s n sigma: AppR (sigma • Lambda (length T + n) s) T >* T .+ sigma • Lambda n s.
Proof.
revert s n sigma; induction T; intros; cbn [AppR length]; (eauto 2).
replace (S (length T) + n) with (length T + S n) by lia.
Admitted.

Lemma AppL_app S1 S2 t: AppL (S1 ++ S2) t = AppL S1 (AppL S2 t).
Proof.
revert S2 t; induction S1; cbn; congruence.
