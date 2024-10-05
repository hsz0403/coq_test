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

Lemma normal_forms_encodes s: normal s -> lambda lambda (ren (add 2) s) (enc 1 (var 1)) ≡ lambda lambda Succ ((ren (add 2) s) (var 1)) -> exists n, encodes s n.
Proof.
remember (add 2) as delta.
cbn; intros H EQ % equiv_lam_elim % equiv_lam_elim; destruct s; cbn in EQ.
-
Injection EQ; Discriminate.
-
Injection EQ; Discriminate.
-
eapply equiv_reduce in EQ.
2, 3: dostep; asimpl; reflexivity.
eapply normal_lam_elim in H.
enough (exists n : nat, forall t delta, t .: delta >> var • s ≡ enc n t) as [n H'] by (exists n; intros t delta'; asimpl; rewrite stepBeta; asimpl; eauto).
induction s as [[] | | |]; unfold funcomp in EQ; cbn in EQ.
+
now (exists 0).
+
Discriminate.
+
Discriminate.
+
Discriminate.
+
eapply head_atom in H as H'; cbn; intuition.
eapply equiv_app_elim in EQ as [EQ1 EQ2]; cbn; intuition.
2: eapply atom_head_lifting; eauto; intros []; cbn; intuition.
enough (s1 = g a).
*
subst.
cbn in EQ2.
eapply IHs2 in EQ2.
2: eauto using normal_app_r.
destruct EQ2.
subst.
exists (S x).
intros t delta; cbn; simplify; now rewrite H0.
*
destruct s1 as [[] | | | t1 t2]; simplify in EQ1; cbn in *.
1 - 4: try Injection EQ1; Discriminate.
assert (isAtom (head (g a (var 1) .: delta >> var • t1))) by (eapply atom_head_lifting; eauto; intros []; cbn; intuition).
Injection EQ1.
assert (isAtom (head t2)).
{
eapply head_atom.
eauto using normal_app_r, normal_app_l.
intros ?; destruct t2; cbn in H2; intuition; Discriminate.
}
assert (isAtom (head (g a (var 1) .: delta >> var • t2))) by (eapply atom_head_lifting; eauto; intros []; cbn; intuition).
destruct t1; cbn in *; try Discriminate.
destruct f; cbn in *; Discriminate.
destruct t2; cbn in *; try Discriminate.
destruct f; cbn in *; Discriminate.
Injection H1; subst.
Injection H2; subst.
reflexivity.
-
eapply normal_ren with (delta0 := delta) in H.
eapply head_atom in H; eauto.
cbn in EQ.
Injection EQ.
Injection H0.
unshelve eapply ren_equiv_proper in H2; [exact (pred >> pred)|exact (pred >> pred)|eauto..]; asimpl in H2.
unshelve eapply ren_equiv_proper in H3; [exact (pred >> pred)|exact (pred >> pred)|eauto..]; asimpl in H3.
exists 1.
intros t delta'; simplify.
subst delta.
asimpl in H3.
asimpl in H2.
now rewrite H2, H3.
