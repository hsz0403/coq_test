Set Implicit Arguments.
Require Import List Lia.
From Undecidability.HOU Require Import std.std calculus.calculus unification.higher_order_unification unification.nth_order_unification.
Set Default Proof Using "Type".
Section ListEnumerability.
Variable (X: Const).
Hypothesis (enumX: enumT X).
Fixpoint L_exp (n: nat) : list (exp X) := match n with | 0 => nil | S n => L_exp n ++ [var x | x ∈ L_T nat n] ++ [const c | c ∈ L_T X n] ++ [lambda s | s ∈ L_exp n] ++ [app s t | (s, t) ∈ (L_exp n × L_exp n)] end.
Global Instance enumT_exp: enumT (exp X).
Proof using enumX.
exists L_exp.
-
eauto.
-
induction x as [y|c|s| s IH1 t IH2].
+
destruct (el_T y).
exists (S x).
cbn.
in_app 2.
now in_collect y.
+
destruct (el_T c).
exists (S x).
cbn.
in_app 3.
now in_collect c.
+
destruct IHs.
exists (S x).
cbn.
in_app 4.
now in_collect s.
+
destruct IH1 as [x1], IH2 as [x2].
exists (S (x1 + x2)).
cbn.
in_app 5.
in_collect (s, t); eapply cum_ge'; eauto.
Fixpoint L_type (n: nat) : list (type) := match n with | 0 => nil | S n => L_type n ++ [typevar x | x ∈ L_T nat n] ++ [A → B | (A, B) ∈ (L_type n × L_type n)] end.
Global Instance enumT_type: enumT type.
Proof.
exists L_type.
-
eauto.
-
induction x as [beta|A IH1 B IH2].
+
destruct (el_T beta).
exists (S x).
cbn.
in_app 2.
now in_collect beta.
+
destruct IH1 as [x1], IH2 as [x2].
exists (S (x1 + x2)).
cbn.
in_app 5.
in_collect (A, B); eapply cum_ge'; eauto.
Fixpoint L_typingT Gamma s A n : list (Gamma ⊢ (s: exp X) : A) := match n with | 0 => nil | S n => L_typingT Gamma s A n ++ match s as s return list (Gamma ⊢ s : A) with | var i => [typingVar Gamma i H where H: nth Gamma i = Some A] | const c => [cast (typingConst Gamma c) H where H : ctype X c = A] | lambda s => match A with | typevar beta => nil | A → B => [ typingLam H | H ∈ L_typingT (A :: Gamma) s B n] end | app s t => [typingApp H1 H2 | (H1, H2) ∈ (L_typingT Gamma s (A1 → A) n × L_typingT Gamma t A1 n) & A1 ∈ L_T n] end end.
Scheme typing_strong_ind := Induction for typing Sort Prop.
Global Instance enumT_typing Gamma (s: exp X) A: enumT (Gamma ⊢ s: A).
Proof.
exists (L_typingT Gamma s A).
-
eauto.
-
intros x.
induction x using typing_strong_ind.
+
exists 1.
cbn.
destruct dec; intuition.
in_app 1.
f_equal.
eapply Eqdep_dec.inj_pair2_eq_dec.
eapply eq_dec.
now destruct e, e0.
+
exists 1.
cbn.
destruct dec; intuition; cbn.
left.
unfold cast; rewrite <-Eqdep_dec.eq_rect_eq_dec; eauto.
decide equality.
decide equality.
+
edestruct IHx as [m].
exists (S m); cbn.
in_app 2.
now in_collect x.
+
edestruct IHx1 as [x1'], IHx2 as [x2'], (el_T A) as [x3'].
exists (S (x1' + x2' + x3')); cbn; in_app 3.
eapply in_flat_map.
exists A.
split.
2: in_collect (x1, x2).
all: eauto using cum_ge'.
Fixpoint L_typing n : list (ctx * exp X * type) := match n with | 0 => nil | S n => L_typing n ++ [(Gamma, s, A) | (Gamma, s, A) ∈ (L_T n × L_T n × L_T n), |@L_T (Gamma ⊢ s : A) _ n| <> 0] end.
Fixpoint L_uni (n: nat) : list (uni X) := match n with | 0 => nil | S n => L_uni n ++ flat_map (fun '(Gamma, s, t, A) => [@Build_uni _ Gamma s t A H1 H2 | (H1, H2) ∈ (L_T n × L_T n)]) [(Gamma, s, t, A) | (Gamma, s, t, A) ∈ (L_T n × L_T n × L_T n × L_T n)] end.
Global Instance enumT_uni : enumT (uni X).
Proof using enumX with eauto using cum_ge'.
exists L_uni.
-
eauto.
-
intros [Gamma s t A H1 H2].
destruct (el_T Gamma) as [x1], (el_T s) as [x2], (el_T t) as [x3], (el_T A) as [x4], (el_T H1) as [x5], (el_T H2) as [x6].
exists (S (x1 + x2 + x3 + x4 + x5 + x6)); cbn.
in_app 2.
eapply in_flat_map.
exists (Gamma, s, t, A).
intuition.
+
in_collect (Gamma, s, t, A); eapply cum_ge'; eauto;lia.
+
in_collect (H1, H2)...
Fixpoint L_subst (tau: fin -> exp X) (n: nat) : list (ctx * (fin -> exp X) * ctx) := match n with | 0 => nil | S n => L_subst tau n ++ [(Delta, tau, nil) | Delta ∈ L_T n] ++ [(Delta, s .: sigma, A :: Gamma) | ((Delta, sigma, Gamma), (Delta', s, A)) ∈ (L_subst (S >> tau) n × L_typing n), Delta = Delta'] end.
Definition Uextended '(I, Delta, sigma) := Delta ⊩ sigma : @Gammaᵤ X I /\ sigma • sᵤ ≡ sigma • tᵤ /\ forall x, x >= |Gammaᵤ| -> sigma x = var x.
Fixpoint L_Uextended (n: nat) : list (uni X * ctx * (fin -> exp X)) := match n with | 0 => nil | S n => L_Uextended n ++ [(I, Delta, sigma) | (I, (Delta, sigma, Gamma)) ∈ (@L_T (uni X) _ n × L_subst var n ), Gamma = Gammaᵤ /\ xi n (sigma • sᵤ) <> None /\ xi n (sigma • tᵤ) <> None /\ xi n (sigma • sᵤ) = xi n (sigma • tᵤ)] end.
End ListEnumerability.

Theorem enumerable_unification (X: Const): enumerable__T X -> enumerable (U X).
Proof.
rewrite enum_enumT.
intros [EX].
eapply enumerable_iff with (P := fun I => exists Delta sigma, Uextended (I, Delta, sigma)).
-
intros [Gamma s t A ? ?]; unfold Uextended, U; cbn; split; intros [Delta [sigma []]].
exists Delta; exists sigma; intuition.
pose (tau x := if nth Gamma x then sigma x else var x).
exists Delta; exists tau; intuition.
unfold tau; intros ?? H'; rewrite H'; eauto.
repeat rewrite subst_extensional with (sigma0 := tau) (tau0 := sigma); eauto.
1 - 2: intros ? H'; assert (x ∈ dom Gamma) as H1 by eauto using typing_variables; unfold tau; now domin H1.
unfold tau.
now eapply nth_error_None in H1 as ->.
-
eapply projection with (p := fun x: uni X * ctx => exists sigma, let (I, Delta) := x in Uextended (I, Delta, sigma)).
eapply projection with (p := @Uextended X).
eapply enumerable_enum; exists (@L_Uextended X EX); eapply enum_unification'.
