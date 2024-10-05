Set Implicit Arguments.
Require Import List Lia Program.Program.
From Undecidability.HOU Require Import std.std axioms.
Require Import RelationClasses Morphisms Wf Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus second_order.goldfarb.encoding.
Require Import FinFun Coq.Arith.Wf_nat.
Import ListNotations.
Set Default Proof Using "Type".
Section Multiplication.
Variable (n: nat).
Implicit Type (X Y: list (nat * nat)).
Hint Rewrite Cons_subst : asimpl.
Hint Rewrite Pair_subst : asimpl.
Notation r := (var 2).
Notation A := (var 1).
Notation B := (var 0).
Let σ p q := B .: A .: ⟨enc p A, enc q B⟩ ::: Nil .: (add 2) >> var.
Let τ := Succ B .: enc n A .: Nil .:((add 2) >> var).
Definition t k := ⟨enc (k * n) A, enc k B⟩.
Definition T k := lambda lambda lambda lin (tab t k) r.
Hint Rewrite T_subst T_ren : asimpl.
Section G_subst.
End G_subst.
Section t_subst.
End t_subst.
Hint Rewrite hat_t_sigma hat_t_tau : asimpl.
Section G_reduce.
End G_reduce.
Definition Grel m p G := lambda lambda (ren (add 2) G) (⟨ enc p A, enc m B⟩ ::: Nil) A B ≡ lambda lambda ⟨ A, B ⟩ ::: (ren (add 2) G) Nil (enc n A) (Succ B).
Section InvertSubstitution.
Variable (p q: nat).
End InvertSubstitution.
Section RecoverStructure.
Fixpoint size_exp {Z} (s: exp Z) := match s with | var _ => 0 | const c => 0 | app s t => S (size_exp s + size_exp t) | lambda s => S (size_exp s) end.
End RecoverStructure.
End Multiplication.

Lemma Cons_subst sigma s t: sigma • (s ::: t) = (sigma • s) ::: (sigma • t).
Proof.
Admitted.

Lemma Cons_injective s s' u u': s ::: u = s' ::: u' -> s = s' /\ u = u'.
Proof.
Admitted.

Lemma Pair_subst sigma s t: sigma • ⟨s, t⟩ = ⟨sigma • s, sigma • t⟩.
Proof.
Admitted.

Lemma Pair_injective s s' u u': ⟨s, u⟩ = ⟨s', u'⟩ -> s = s' /\ u = u'.
Proof.
Admitted.

Lemma T_subst m sigma: sigma • (T m) = T m.
Proof.
unfold T; cbn; asimpl.
rewrite !map_id_list; eauto.
rewrite tab_map_nats.
intros; mapinj.
Admitted.

Lemma T_ren m delta: ren delta (T m) = T m.
Proof.
Admitted.

Lemma G_right_subst m: (T m) Nil (enc n A) (Succ B) ≡ τ • lin (tab t m) r.
Proof.
rewrite <-T_ren with (delta := add 2).
unfold T.
eapply equiv_join.
cbn.
do 3 (dostep; cbn).
unfold beta.
rewrite rinstInst_exp, !compComp_exp.
reflexivity.
eapply refl_star.
eapply ext_exp.
intros [|[|[]]]; cbn; eauto.
Admitted.

Lemma hat_t_sigma p q k: σ p q • t k = t k.
Proof.
Admitted.

Lemma hat_t_tau k: τ • t k = t (S k).
Proof.
cbn; asimpl; cbn; simplify.
rewrite <-!enc_app.
Admitted.

Lemma G_left_reduce m p q: (T m) (⟨ enc p A, enc q B⟩ ::: Nil) A B ≡ lin (tab t m) (⟨ enc p A, enc q B⟩ ::: Nil).
Proof.
rewrite G_left_subst.
asimpl.
rewrite map_id_list; eauto.
rewrite tab_map_nats.
intros; mapinj.
Admitted.

Lemma G_right_reduce m: (T m) Nil (enc n A) (Succ B) ≡ lin (tab (S >> t) m) Nil.
Proof.
rewrite G_right_subst.
asimpl.
eapply eq_equiv.
f_equal.
rewrite tab_map.
eapply tab_ext.
intros ?; unfold funcomp, t; cbn; asimpl.
unfold Pair, τ; cbn.
f_equal.
f_equal.
rewrite <-enc_app.
f_equal; lia.
Admitted.

Lemma G_forward m: Grel m (m * n) (T m).
Proof.
unfold Grel.
asimpl.
do 2 eapply equiv_lam_proper.
unfold Cons at 2.
rewrite G_left_reduce, G_right_reduce.
rewrite <-lin_cons.
change (⟨ A, B ⟩) with (t 0).
rewrite <-tab_S.
change (_ ::: _) with (lin [t m] Nil).
Admitted.

Lemma multiplication_lambdas M m p: normal M -> Grel m p M -> (exists M', M = (lambda lambda lambda M') /\ σ p m • M' = t 0 ::: (τ • M')).
Proof.
unfold Grel, Pair, Cons.
cbn.
intros Nu EQ.
remember (fun m : nat => S (S m)) as delta.
rename M into u.
assert (normal (ren delta u)) as N' by (subst; eapply normal_ren; eauto).
do 2 apply equiv_lam_elim in EQ.
destruct u as [| | u' | ]; unfold funcomp; cbn in EQ.
4: eapply head_atom in N'; eauto.
1, 2, 4: Injection EQ; Injection H; Discriminate.
rewrite stepBeta in EQ; eauto.
asimpl in EQ.
rewrite stepBeta in EQ; eauto.
asimpl in EQ.
destruct u' as [[]| | u' | ]; cbn in EQ.
1 - 3: Injection EQ; Injection H; Discriminate.
-
do 2 (rewrite stepBeta in EQ; eauto; asimpl in EQ; cbn in EQ).
destruct u' as [[|[]] | | u' | u1 u2 ]; cbn in EQ.
1 - 4: Injection EQ; unfold funcomp in *; Discriminate.
+
exists u'.
intuition.
do 2 (rewrite stepBeta in EQ; eauto; asimpl in EQ; cbn in EQ).
repeat eapply normal_lam_elim in Nu.
eapply equiv_unique_normal_forms; [eauto | eauto |idtac..].
subst delta; exact EQ.
2: eapply normal_app_intro; cbn; intuition.
2: repeat eapply normal_app_intro; eauto.
all: eapply normal_subst; try eassumption.
all: intros [|[|[]]]; cbn; eauto 2.
all: unfold funcomp, Nil; (repeat eapply normal_app_intro); eauto 2.
destruct n; simplify; eauto.
+
exfalso.
repeat eapply normal_lam_elim in Nu.
eapply head_atom in Nu as H'; eauto.
eapply atom_head_lifting with (sigma := A .: g (g (enc p A) (enc m B)) (id Nil) .: delta >> var) in H' as H4.
2: intros [|[]]; cbn; eauto.
cbn in H4.
Injection EQ.
Injection H.
destruct u1 as [[|[]]|[]| |]; cbn in H1; try Injection EQ; try Discriminate.
-
eapply normal_lam_elim in Nu.
eapply head_atom in Nu; eauto.
eapply atom_head_lifting with (sigma := g (g (enc p A) (enc m B)) Nil .: delta >> var) in Nu; cbn in Nu.
2: intros []; cbn; eauto.
Injection EQ.
Injection H.
Admitted.

Lemma subst_var_a s': σ p q • s' = A -> s' = A.
Proof.
intros H4.
destruct s'; try discriminate.
cbn in H4.
Admitted.

Lemma subst_var_b s': σ p q • s' = B -> s' = B.
Proof.
intros H4.
destruct s'; try discriminate.
cbn in H4.
Admitted.

Lemma subst_enc k e u: σ p q • e = enc k u -> exists e', e = enc k e' /\ σ p q • e' = u.
Proof using τ n.
induction k in e |-*; cbn.
-
intros; eexists; intuition; eauto.
-
intros.
simplify in *.
destruct e as [ [| [| []]] | | | e1 e3 ]; try discriminate.
destruct e1 as [ [| [| []]] | | | e1 e2 ]; try discriminate.
destruct e1 as [ [| [| []]] | [] | | ]; try discriminate.
destruct e2 as [ [| [| []]] | [[]|] | | ]; try discriminate.
simplify in H.
injection H as H.
destruct (IHk _ H) as [e']; intuition; subst.
exists e'.
simplify.
Admitted.

Lemma G_left_subst m p q: (T m) (⟨ enc p A, enc q B⟩ ::: Nil) A B ≡ σ p q • (lin (tab t m) r).
Proof.
rewrite <-T_ren with (delta := add 2).
unfold T.
eapply equiv_join.
cbn.
do 3 (dostep; cbn).
unfold beta.
rewrite rinstInst_exp, !compComp_exp.
reflexivity.
eapply refl_star.
eapply ext_exp.
intros [|[|[]]]; cbn; eauto.
now asimpl.
