Set Implicit Arguments.
Require Import RelationClasses Morphisms List Lia Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus second_order.diophantine_equations systemunification nth_order_unification.
Import ListNotations.
Set Default Proof Using "Type".
Definition ag : Const := {| const_type := option (option False); ctype := fun o => match o with | None => alpha → alpha → alpha | Some None => alpha | Some (Some f) => match f with end end; |}.
Notation g := (@const ag None).
Notation a := (@const ag (Some None)).
Hint Resolve typing_a typing_g : core.
Section Linearization.
Implicit Types (S: list (exp ag)).
Definition lin S t := AppL (map (app g) S) t.
Hint Rewrite lin_nil lin_cons lin_app : simplify.
Hint Rewrite lin_ren lin_subst : asimpl.
End Linearization.
Hint Rewrite lin_ren lin_subst : asimpl.
Hint Rewrite lin_nil lin_cons lin_app : simplify.
Section Encoding.
Notation Succ := (g a).
Definition enc n s := lin (repeat a n) s.
Definition encodes s n := forall t delta, (ren delta s) t ≡ enc n t.
Arguments enc : simpl never.
Section enc_equations.
Hint Rewrite enc_zero : simplify.
Hint Rewrite enc_succ : simplify.
Hint Rewrite enc_succ_out : simplify.
Hint Rewrite enc_app : simplify.
End enc_equations.
Hint Rewrite enc_app enc_succ_out enc_succ enc_zero : simplify.
Hint Rewrite enc_ren enc_subst : asimpl.
Hint Resolve enc_normal : core.
Global Instance enc_equiv: Proper (Logic.eq ++> equiv step ++> equiv step) enc.
Proof.
intros ?? -> ??; unfold enc, lin; now intros ->.
End Encoding.
Hint Resolve enc_normal : core.
Hint Rewrite enc_zero enc_succ enc_app enc_succ_out: simplify.
Hint Rewrite enc_ren enc_subst: asimpl.
Arguments enc : simpl never.
Notation Succ := (g a).
Section Variables.
Definition F (x: nat): nat := (I__S (inl x)).
Definition G (x y z: nat): nat := I__S (inr (I__P (x, I__P (y, z)))).
Definition Fs E := map F (Vars__de E).
Definition Gs (E: list deq) := flat_map (fun e => match e with | (x *ₑ y =ₑ z) => [G x y z] | _ => nil end) E.
End Variables.
Arguments F : simpl never.
Arguments G : simpl never.
Arguments Fs : simpl never.
Arguments Gs : simpl never.
Hint Resolve F_not_in_G G_not_in_F : core.
Section Equations.
Implicit Types (x y z: nat).
Definition Cons s t := g s t.
Notation "s ::: t" := (Cons s t) (at level 62).
Definition Nil := a.
Definition Pair s t := g s t.
Notation "⟨ s , t ⟩" := (Pair s t) (at level 60).
Definition varEQ x: eq ag := (lambda lambda var (2 + F x) (Succ (var 1)), lambda lambda Succ (var (2 + F x) (var 1))).
Definition constEQ x: eq ag := (lambda lambda (var (2 + F x)) (var 0), lambda lambda enc 1 (var 0)).
Definition addEQ x y z: eq ag := (lambda lambda var (2 + F x) (var (2 + F y) (var 1)), lambda lambda var (2 + F z) (var 1)).
Definition mulEQ x y z : eq ag := (lambda lambda var (2 + G x y z) (⟨var (2 + F z) (var 1), var (2 + F x) (var 0)⟩ ::: Nil) (var 1) (var 0) , lambda lambda ⟨var 1, var 0⟩ ::: var (2 + G x y z) Nil (var (2 + F y) (var 1)) (Succ (var 0))).
Definition eqs (e: deq) : eqs ag := match e with | x =ₑ 1 => [varEQ x; constEQ x] | x +ₑ y =ₑ z => [varEQ x; varEQ y; varEQ z; addEQ x y z] | x *ₑ y =ₑ z => [varEQ x; varEQ y; varEQ z; mulEQ x y z] end.
Notation Eqs E := (flat_map eqs E).
End Equations.
Notation Eqs E := (flat_map eqs E).
Notation "s ::: t" := (Cons s t) (at level 62).
Notation "⟨ s , t ⟩" := (Pair s t) (at level 60).
Section Typing.
Variable (E: list deq).
Definition Gamma__deq := tab (fun x => if partition_F_G x then (alpha → alpha) else (alpha → alpha → alpha → alpha)) (S (Sum (Fs E) + Sum (Gs E))).
Arguments Gamma__deq: simpl never.
Hint Resolve typing_G typing_F : core.
Ltac autotype := repeat match goal with | [|- _ ⊢(2) var (?n + ?x) : _] => eapply ordertyping_preservation_under_renaming with (delta := add n) (s := var x) | [|- _ ⊢(2) var (G _ _ _) : _ ]=> eapply typing_G | [|- _ ⊢(2) var (F _) : _ ]=> eapply typing_F | [|- _ ⊢(2) var ?n : _] => now (econstructor; cbn; eauto) | [|- _ ⊢(2) const _ : _] => eauto | [|- _ ⊢(2) enc _ _ : _] => eapply enc_typing | [|- _ ⊢(2) _ : _] => econstructor | [|- _ ⊫ add _ : _] => now intros ?? | [H: ?e ∈ E |- _ ∈ Vars__de E] => eapply Vars__de_in; [eapply H|cbn;intuition] end.
End Typing.
Program Instance H10_to_SOU (E: list deq): ordsysuni ag 2 := { Gamma₀' := Gamma__deq E; E₀' := Eqs E; L₀' := repeat (alpha → alpha → alpha) (length (Eqs E)); H₀' := _; }.
Next Obligation.
eapply ordertyping_combine; eapply repeated_ordertyping; unfold left_side, right_side; simplify; eauto 1.
all: intros ? ?; mapinj; eapply in_flat_map in H1 as []; intuition.
all: eapply typing_equations; eauto.

Lemma encodes_characeristic s n: encodes s n -> lambda lambda (ren (add 2) s) (enc 1 (var 0)) ≡ lambda lambda g a ((ren (add 2) s) (enc 0 (var 0))).
Proof.
Admitted.

Lemma disjoint_F_G x m n p: F x <> G m n p.
Proof.
intros H.
unfold F, G in H; eapply injective_I__S in H.
Admitted.

Lemma F_injective x y: F x = F y -> x = y.
Proof.
intros H; unfold F in H; eapply injective_I__S in H.
Admitted.

Lemma G_injective a b c x y z: G a b c = G x y z -> a = x /\ b = y /\ c = z.
Proof.
intros H; unfold G in H; eapply injective_I__S in H.
injection H as H.
apply injective_I__P in H; injection H as ? H.
apply injective_I__P in H; injection H as ? H.
Admitted.

Lemma partition_F_G: forall h, { x | F x = h } + { '(x, y, z) | G x y z = h } .
Proof.
intros h.
unfold F, G.
destruct (R__S h) eqn: H1.
+
left.
exists n.
rewrite <-H1.
now rewrite I__S_R__S.
+
right.
destruct (R__P n) as [a n'] eqn: H2.
destruct (R__P n') as [b c] eqn: H3.
exists (a, b, c).
apply (f_equal I__S) in H1.
apply (f_equal I__P) in H2.
apply (f_equal I__P) in H3.
rewrite ?I__P_R__P, ?I__S_R__S in *.
Admitted.

Lemma Fs_in x E: x ∈ Vars__de E -> F x ∈ Fs E.
Proof.
intros; eapply in_map_iff.
Admitted.

Lemma Gs_in x y z E: (x *ₑ y =ₑ z) ∈ E -> G x y z ∈ Gs E.
Proof.
intros; eapply in_flat_map.
exists (x *ₑ y =ₑ z).
Admitted.

Lemma in_Fs y E: y ∈ Fs E -> exists x, F x = y /\ x ∈ Vars__de E.
Proof.
Admitted.

Lemma in_Gs y E: y ∈ Gs E -> exists a b c, G a b c = y /\ (a *ₑ b =ₑ c) ∈ E.
Proof.
intros H; unfold Gs in *; eapply in_flat_map in H.
destruct H as [[]]; cbn in *; intuition.
subst.
exists x; exists y0; exists z.
Admitted.

Lemma F_not_in_G x E: ~ F x ∈ Gs E.
Proof.
intros (a & b & c & []) % in_Gs.
Admitted.

Lemma G_not_in_F x y z E: ~ G x y z ∈ Fs E.
Proof.
intros (a & []) % in_Fs.
Admitted.

Lemma in_Equations q E: q ∈ Eqs E <-> (exists e, e ∈ E /\ q ∈ eqs e).
Proof.
Admitted.

Lemma Gamma__deq_nth_F h: h ∈ Fs E -> nth Gamma__deq h = Some (alpha → alpha).
Proof.
intros H.
unfold Gamma__deq.
rewrite tab_nth.
destruct (partition_F_G) as [[x ?]|[[[x y] z] ? ]]; subst; intuition.
eapply G_not_in_F in H as [].
eapply Sum_in in H.
Admitted.

Lemma Gamma__deq_nth_G h: h ∈ Gs E -> nth Gamma__deq h = Some (alpha → alpha → alpha → alpha).
Proof.
intros H.
unfold Gamma__deq.
rewrite tab_nth.
destruct (partition_F_G) as [[x ?]|[[[x y] z] ? ]]; subst; intuition.
eapply F_not_in_G in H as [].
eapply Sum_in in H.
Admitted.

Lemma nth_Gamma__deq_F x A: nth Gamma__deq (F x) = Some A -> A = alpha → alpha.
Proof.
intros H.
eapply nth_error_Some_lt in H as H'.
unfold Gamma__deq in *.
rewrite tab_nth in H; simplify in *; eauto.
destruct partition_F_G as [[]| [[[]] ?]].
congruence.
Admitted.

Lemma nth_Gamma__deq_G x y z A: nth Gamma__deq (G x y z) = Some A -> A = alpha → alpha → alpha → alpha.
Proof.
intros H.
eapply nth_error_Some_lt in H as H'.
unfold Gamma__deq in *; simplify in *.
rewrite tab_nth in H; simplify in *; eauto.
destruct partition_F_G as [[]| [[[]] ?]].
exfalso; eapply disjoint_F_G; eauto.
Admitted.

Lemma Gamma__deq_content A : A ∈ Gamma__deq -> A = alpha → alpha \/ A = alpha → alpha → alpha → alpha.
Proof.
intros H; unfold Gamma__deq in *.
remember (S (Sum _ + Sum _)) as n.
clear Heqn.
induction n; cbn in *; intuition.
eapply in_app_iff in H; cbn in *; intuition.
Admitted.

Lemma ord_Gamma__deq: ord' Gamma__deq <= 2.
Proof.
unfold Gamma__deq; remember (S (Sum _ + Sum _)) as n.
clear Heqn.
induction n; cbn; simplify; cbn; eauto.
rewrite IHn; simplify.
destruct (partition_F_G).
Admitted.

Lemma typing_F x: x ∈ Vars__de E -> Gamma__deq ⊢(2) @var ag (F x) : alpha → alpha.
Proof.
intros H.
econstructor.
cbn; eauto.
Admitted.

Lemma typing_G x y z: (x *ₑ y =ₑ z) ∈ E -> Gamma__deq ⊢(2) @var ag (G x y z) : alpha → alpha → alpha → alpha.
Proof.
intros H.
econstructor.
cbn; eauto.
Admitted.

Lemma typing_const x: x =ₑ 1 ∈ E -> Gamma__deq ⊢₂(2) constEQ x : alpha → alpha → alpha.
Proof.
Admitted.

Lemma typing_add x y z: x +ₑ y =ₑ z ∈ E -> Gamma__deq ⊢₂(2) addEQ x y z : alpha → alpha → alpha.
Proof.
Admitted.

Lemma typing_mul x y z: x *ₑ y =ₑ z ∈ E -> Gamma__deq ⊢₂(2) mulEQ x y z : alpha → alpha → alpha.
Proof.
Admitted.

Lemma typing_equations q e: e ∈ E -> q ∈ eqs e -> Gamma__deq ⊢₂(2) q : alpha → alpha → alpha.
Proof.
intros H H1; destruct e; cbn in H1; intuition; subst; eauto using typing_const, typing_add, typing_mul.
Admitted.

Lemma typing_var_eq x: x ∈ Vars__de E -> Gamma__deq ⊢₂(2) varEQ x : alpha → alpha → alpha.
Proof.
intros; unfold varEQ; split; cbn [fst snd].
all: autotype; eauto.
