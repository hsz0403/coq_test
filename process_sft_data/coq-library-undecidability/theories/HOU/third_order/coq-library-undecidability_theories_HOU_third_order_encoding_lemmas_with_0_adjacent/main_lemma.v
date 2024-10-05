Set Implicit Arguments.
Require Import RelationClasses Morphisms List Lia Arith Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus third_order.pcp.
Import ListNotations.
Set Default Proof Using "Type".
Section Encoding.
Context {X: Const}.
Variable (u v: nat).
Hypothesis (u_neq_v: u <> v).
Definition encb (b: symbol) : exp X := var (if b then u else v).
Definition enc (w: word) : exp X := lambda (AppL (renL shift (map encb w)) (var 0)).
Notation Enc := (map enc).
Section Typing.
End Typing.
Section Reduction.
Hint Rewrite enc_nil enc_cons : simplify.
Hint Rewrite enc_app : simplify.
End Reduction.
Hint Rewrite enc_nil enc_cons enc_app : simplify.
Section Substitution.
End Substitution.
Definition nostring (t: exp X) := forall s, ~ t ≡ var u s /\ ~ t ≡ var v s.
Section Injectivity.
End Injectivity.
Section EquivalenceInversion.
Variables (s t: exp X) (x: nat) (sigma: fin -> exp X) (S: list (exp X)).
Hypothesis (H1: forall y, isVar (sigma y) /\ sigma y <> var x).
Hypothesis (N: normal s).
Hypothesis (EQ: S .+ sigma • s ≡ (var x) t).
End EquivalenceInversion.
Section MainLemma.
Variable (Gamma : ctx) (s: exp X) (n: nat).
Hypothesis (Ts: Gamma ⊢(3) s : Arr (repeat (alpha → alpha) n) alpha).
Hypothesis (Vu: ~ u ∈ vars s) (Vv: ~ v ∈ vars s).
End MainLemma.
End Encoding.
Hint Rewrite @enc_app @enc_nil: simplify.
Notation Enc u v := (map (enc u v)).
Section ReductionEncodings.
Context {X: Const}.
Definition finst I n := Lambda n (AppL (map var I) (@var X n)).
End ReductionEncodings.

Lemma main_lemma: exists I, I ⊆ nats n /\ forall W, |W| = n -> exists t, AppR s (Enc W) ≡ AppL (select I (Enc W)) t /\ nostring t.
Proof using u_neq_v Vv Vu Ts Gamma.
pose (mv := fun x => match x == u, x == v with right _,right _ => x | _,_ => S(u + v + x) end).
assert (forall x, mv x >= x) as GE.
{
eauto; intros; unfold funcomp; intuition idtac; unfold mv in *.
eauto; intros; edestruct eq_dec; [lia|]; destruct eq_dec; (eauto 3).
}
assert (forall x, var (mv x) <> @var X u) as Nu.
{
intros x H; injection H; unfold mv; destruct eq_dec; [lia|]; destruct eq_dec; [lia|].
intros; subst; (eauto 2).
}
assert (forall x, var (mv x) <> @var X v) as Nv.
{
intros x H; injection H; unfold mv; destruct eq_dec; [lia|]; destruct eq_dec; [lia|].
intros; subst; (eauto 2).
}
replace s with (ren mv s).
2: {
asimpl; erewrite subst_extensional with (tau := var); asimpl; (eauto 2).
intros; unfold funcomp, mv; destruct eq_dec; subst; [exfalso; eapply Vu; eauto|].
destruct eq_dec; subst; [exfalso; eapply Vv; eauto|eauto].
}
eapply ordertyping_termination_steps in Ts as N; destruct N as [t [E N]].
eapply normal_nf in N as N2.
destruct N2 as [k a ? T _ isA ->].
eapply ordertyping_preservation_under_steps in Ts as Tv; (eauto 2).
eapply Lambda_ordertyping_inv in Tv as (L & B & H0 & H1 & <-).
destruct (Nat.lt_total n (|L|)) as [?|[?|?]].
-
exfalso.
eapply (f_equal arity) in H1; simplify in H1; lia.
-
destruct (AppL_decomposition (AppR a T) n) as [[I v''] (H2&H3&H4)].
exists I.
intuition.
exists (Enc W .+ mv >> var • v'').
split.
+
rewrite E.
rewrite Lambda_ren, AppR_Lambda'; simplify; try congruence.
rewrite it_up_var_sapp, H3, AppL_subst, select_variables_subst; simplify; (eauto 2).
all: rewrite ?H5; (eauto 2).
+
eapply Arr_inversion in H1 as [[] [H1 H6]]; simplify; try lia.
2: discriminate.
cbn in H1, H6.
simplify in H1.
subst.
rewrite H3 in H0; eapply AppL_ordertyping_inv in H0 as (?&?&?&?).
split; intros EQ; eapply end_is_var_typed in EQ as (? & ? & ? & ?).
1, 6: eapply H4; simplify in H6; (eauto 1); rewrite <-H5; (eauto 2).
3, 7: eauto.
1, 4: intros; unfold funcomp; intuition eauto.
1, 3: rewrite H3 in N; eapply normal_AppL_right, normal_Lambda, N.
all: simplify; rewrite H1 in H0; simplify in H0; rewrite <-H5 in H0; (eauto 2).
-
remember mv as delta.
exists nil; intuition; cbn; simplify.
eexists.
rewrite E.
intuition eauto.
edestruct (@list_decompose_alt (length L) _ W) as (W1&W2&?&?); subst; (eauto 2).
simplify.
rewrite !AppR_app, !Lambda_ren.
split; rewrite !AppR_Lambda'; simplify; (eauto 2).
all: rewrite !it_up_var_sapp; simplify; (eauto 1); rewrite AppR_subst.
all: intros EQ.
all: destruct a as [y| d | |]; cbn in isA; intuition; [destruct (le_lt_dec (length W2) y)|].
all: revert EQ.
3, 6: cbn; intros EQ' % equiv_head_equal; cbn; simplify; cbn; auto 1.
3, 4: simplify in EQ'; cbn in EQ'; subst; discriminate.
1, 3: cbn; rewrite sapp_ge_in; simplify; (eauto 2).
1, 2: intros EQ' % equiv_head_equal; cbn; simplify; cbn; auto 1.
1, 2: simplify in EQ'; cbn in EQ'; subst; (eauto 2).
all: eapply AppR_ordertyping_inv in H0 as [? [_ T2]]; intuition idtac; inv T2.
all: symmetry in H1; eapply Arr_inversion in H1 as H6; simplify; try lia.
all: destruct H6 as (?&?&?); eapply repeated_app_inv in H0.
all: intuition; subst; rewrite H0 in *; simplify in H4; simplify in H3; rewrite H4 in l.
all: eapply id in H3 as HH; rewrite nth_error_app1, nth_error_repeated in HH; simplify; (eauto 2).
all: injection HH as HH; destruct x0; simplify in H6; simplify in H3.
all: simplify in H; try lia; cbn in H8; injection H8 as ->.
all: eapply (f_equal ord) in HH; simplify in HH.
all: symmetry in HH; eapply Nat.eq_le_incl in HH; simplify in HH.
all: intuition; cbn [ord'] in H9.
all: cbn [add] in H9; rewrite Max.succ_max_distr in H9.
all: eapply Nat.max_lub_l in H9; cbn in H9; lia.
