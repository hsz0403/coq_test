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

Lemma dec_enc: forall s, normal s -> { n | s a ≡ enc n a } + ({ n | s a ≡ enc n a } -> False).
Proof.
intros s N.
specialize (@red_fun_rho _ (@step ag) (@par ag) rho) as f.
do 4 mp f; try typeclasses eauto; eauto.
assert (s a ▷ rho (s a)).
-
eapply id in f as g.
destruct g as [H1 H2].
split; [eauto|].
destruct s; cbn.
+
eapply normal_app_intro; eauto.
+
eapply normal_app_intro; eauto.
+
eapply normal_subst.
1 - 2: intros []; cbn; eauto.
enough (rho s = s) as -> by eauto using normal_lam_elim.
eapply red_fun_fp; eauto using normal_lam_elim.
+
eapply head_atom in N as isA; [|eauto].
assert (rho s1 = s1) as -> by (eapply red_fun_fp; eauto using normal_app_l, normal_app_r).
assert (rho s2 = s2) as -> by (eapply red_fun_fp; eauto using normal_app_l, normal_app_r).
destruct s1; cbn in isA; intuition.
-
destruct (dec_enc_eq (rho (s a))) as [[n H1]|H1].
+
left.
exists n.
rewrite H1 in H.
eapply equiv_join.
rewrite H.
all: eauto.
+
right.
intros [n H2].
eapply H1.
exists n.
eapply equiv_unique_normal_forms; eauto.
2: eapply H.
rewrite <-H2.
symmetry.
eapply equiv_join.
rewrite H.
Admitted.

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
Admitted.

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
intros; eapply f; subst; now (exists n).
