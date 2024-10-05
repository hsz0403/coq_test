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

Lemma typing_g Gamma: Gamma ⊢(2) g : alpha → alpha → alpha.
Proof.
Admitted.

Lemma lin_nil t: lin nil t = t.
Proof.
Admitted.

Lemma lin_cons s S t: lin (s :: S) t = g s (lin S t).
Proof.
Admitted.

Lemma lin_app S1 S2 t: lin (S1 ++ S2) t = lin S1 (lin S2 t).
Proof.
Admitted.

Lemma lin_typing Gamma S t: (Gamma ⊢₊(2) S : repeat alpha (length S)) -> (Gamma ⊢(2) t : alpha) -> Gamma ⊢(2) lin S t : alpha.
Proof.
intros ? ?.
induction S as [|s S IH]; simplify; [eauto|].
inv H.
Admitted.

Lemma lin_ren delta S t: ren delta (lin S t) = lin (renL delta S) (ren delta t).
Proof.
Admitted.

Lemma lin_subst sigma S t: sigma • lin S t = lin (sigma •₊ S) (sigma • t).
Proof.
Admitted.

Lemma lin_injective S T s t: length S = length T -> lin S s = lin T t -> S = T /\ s = t.
Proof.
induction S in T |-*; destruct T; try discriminate; simplify in *; eauto.
intros; edestruct IHS.
all: injection H as H; eauto.
Admitted.

Lemma largest_lin s: exists S t, s = lin S t /\ forall s' t', t <> g s' t'.
Proof.
edestruct (AppL_largest s (P := fun (s: exp ag) => match s with app (const None) s => True | _ => False end)) as (S & t & H1 & H2 & H3).
intros [| | | [| [] | | ]].
1 - 8: firstorder.
subst.
enough (exists S', S = map (app g) S') as [S' ->].
exists S'.
exists t.
intuition.
eapply H3; cbn; eauto; cbn; eauto.
clear H3.
induction S.
now (exists nil).
specialize (H1 a) as H2; mp H2; intuition; destruct a as [| | | [| [] | | ]]; intuition.
edestruct IHS as [S']; intros.
eapply H1; intuition.
subst.
Admitted.

Lemma lin_normal S t: (forall s, s ∈ S -> normal s) -> normal t -> normal (lin S t).
Proof.
intros; induction S; cbn; [eauto|].
Admitted.

Lemma enc_zero t: enc 0 t = t.
Proof.
Admitted.

Lemma enc_succ n t: enc (S n) t = Succ (enc n t).
Proof.
Admitted.

Lemma enc_succ_out n t: enc n (Succ t) = Succ (enc n t).
Proof.
Admitted.

Lemma enc_app n m t: enc (n + m) t = enc n (enc m t).
Proof.
Admitted.

Lemma enc_ren delta n s: ren delta (enc n s) = enc n (ren delta s).
Proof.
Admitted.

Lemma enc_subst sigma n s: sigma • enc n s = enc n (sigma • s).
Proof.
Admitted.

Lemma enc_normal n s: normal s -> normal (enc n s).
Proof.
intros; induction n; simplify.
-
eauto.
-
Admitted.

Lemma enc_injective n m s t: isAtom s -> isAtom t -> enc n s ≡ enc m t -> n = m /\ s = t.
Proof.
induction n in m |-*; simplify in *; destruct m; simplify in *; intros.
-
intuition.
destruct s, t; cbn in *; intuition; try Discriminate; Injection H1; congruence.
-
destruct s; cbn in *; intuition; Discriminate.
-
destruct t; cbn in *; intuition; Discriminate.
-
Injection H1.
eapply IHn in H3; eauto.
Admitted.

Lemma enc_typing Gamma s n: (Gamma ⊢(2) s : alpha) -> Gamma ⊢(2) enc n s : alpha.
Proof.
intros; unfold enc.
eapply lin_typing; eauto.
eapply repeated_ordertyping; [|eauto].
intros ? <- % repeated_in.
Admitted.

Lemma dec_enc_eq : forall s, { n | s = enc n a } + ({ n | s = enc n a } -> False).
Proof.
induction s as [| [[[]|]|] | | s1 IH1 s3 IH3].
all: try (right; intros [[|n] ]; cbn; discriminate).
-
left.
exists 0.
reflexivity.
-
destruct IH3 as [[n]|]; subst.
+
destruct s1 as [| | | s1 s2 ].
all: try (right; intros [[|n'] ]; cbn; discriminate).
destruct s1 as [| [[]|] | | ].
all: try (right; intros [[|n'] ]; cbn; discriminate).
destruct s2 as [| [[]|] | | ].
all: try (right; intros [[|n'] ]; cbn; discriminate).
left.
exists (S n).
reflexivity.
+
right.
intros [n H].
destruct n; try discriminate; cbn in *; injection H.
Admitted.

Lemma typing_a Gamma: Gamma ⊢(2) a : alpha.
Proof.
econstructor; cbn; eauto.
