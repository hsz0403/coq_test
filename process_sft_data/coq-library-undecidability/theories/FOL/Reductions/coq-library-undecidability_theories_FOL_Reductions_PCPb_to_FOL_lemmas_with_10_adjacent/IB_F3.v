From Undecidability.PCP Require Import PCP Util.PCP_facts.
From Undecidability.FOL Require Import Util.Deduction Util.Tarski Util.Syntax_facts FOL.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
Require Import Undecidability.PCP.Reductions.PCPb_iff_dPCPb.
Local Definition BSRS := list(card bool).
Local Notation "x / y" := (x, y).
Notation t_f b t := (func (s_f b) (Vector.cons _ t _ (Vector.nil _))).
Notation t_e := (func s_e (Vector.nil _)).
Notation Pr t t' := (@atom _ sig_pred _ _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).
Notation Q := (atom sQ (Vector.nil _)).
Notation i_f b i := (@i_func _ _ _ _ (s_f b) (Vector.cons _ i _ (Vector.nil _))).
Notation i_Pr i i' := (@i_atom _ _ _ _ sPr (Vector.cons _ i _ (Vector.cons _ i' _ (Vector.nil _)))).
Section validity.
Context {ff : falsity_flag}.
Variable R : BSRS.
Fixpoint prep (x : string bool) (t : term) : term := match x with | nil => t | b::x => t_f b (prep x t) end.
Definition enc s := (prep s t_e).
Fixpoint iprep {domain} {I : interp domain} (x : list bool) (y : domain) := match x with | nil => y | b::x => i_f b (iprep x y) end.
Definition F1 := map (fun '(x,y) => Pr (enc x) (enc y)) R.
Definition F2 := map (fun '(x, y) => ∀ ∀ Pr $1 $0 --> Pr (prep x $1) (prep y $0)) R.
Definition F3 := (∀ Pr $0 $0 --> Q).
Definition F : form := F1 ==> F2 ==> F3 --> Q.
Global Instance IB : interp (string bool).
Proof.
split; intros [] v.
-
exact (b :: Vector.hd v).
-
exact nil.
-
exact (derivable R (Vector.hd v) (Vector.hd (Vector.tl v))).
-
exact (dPCPb R).
Defined.
Definition ctx_S := F3 :: rev F2 ++ rev F1.
End validity.
Hint Resolve stack_enum form_discrete : core.
Definition UA := ~ enumerable (complement PCPb).
Module NonStan.
Section Nonstan.
Variable R : BSRS.
Context {ff : falsity_flag}.
Instance IB : interp (option (string bool)).
Proof.
split; intros [] v.
-
exact (match Vector.hd v with Some u => Some (b :: u) | None => None end).
-
exact (Some nil).
-
exact (match Vector.hd v, Vector.hd (Vector.tl v) with Some u, Some v => derivable R u v | _, _ => True end).
-
exact False.
Defined.
End Nonstan.
End NonStan.

Lemma prep_app x y t : prep (x ++ y) t = prep x (prep y t).
Proof.
induction x; cbn; trivial.
Admitted.

Lemma iprep_eval domain (I : interp domain) rho x s : eval rho (prep x s) = iprep x (eval rho s).
Proof.
induction x; cbn; trivial.
Admitted.

Lemma iprep_app domain (I : interp domain) x y d : iprep (x ++ y) d = iprep x (iprep y d).
Proof.
induction x; cbn; trivial.
Admitted.

Lemma IB_prep rho s t : eval rho (prep s t) = s ++ eval rho t.
Proof.
induction s; cbn; trivial.
rewrite <- IHs.
Admitted.

Lemma IB_enc rho s : eval rho (enc s) = s.
Proof.
unfold enc.
rewrite IB_prep.
cbn.
Admitted.

Lemma IB_drv rho t1 t2 : rho ⊨ (Pr t1 t2) <-> derivable R (eval rho t1) (eval rho t2).
Proof.
cbn.
Admitted.

Lemma IB_F1 rho : rho ⊫ F1.
Proof.
unfold F1.
intros ? ([x y] & <- & ?) % in_map_iff.
cbn.
econstructor.
Admitted.

Lemma IB_F2 rho : rho ⊫ F2.
Proof.
unfold F2.
intros ? ([x y] & <- & ?) % in_map_iff u v ?.
cbn.
rewrite !IB_prep.
cbn in *.
Admitted.

Lemma IB_F rho : rho ⊨ F -> dPCPb R.
Proof.
intros H.
unfold F in H.
rewrite !impl_sat in H.
eapply H.
-
eapply IB_F1.
-
eapply IB_F2.
-
Admitted.

Lemma drv_val domain (I : interp domain) rho u v : derivable R u v -> rho ⊨ (F1 ==> F2 ==> Pr (enc u) (enc v)).
Proof.
rewrite !impl_sat.
intros.
induction H.
-
eapply H0.
eapply in_map_iff.
exists (x/y).
eauto.
-
eapply (H1 (∀ ∀ Pr $1 $0 --> Pr (prep x $1) (prep y $0))) in IHderivable.
+
cbn in *.
unfold enc in *.
rewrite !iprep_eval in *.
cbn in *.
rewrite <- !iprep_app in IHderivable.
eapply IHderivable.
+
eapply in_map_iff.
exists (x/y).
Admitted.

Theorem BPCP_valid : PCPb R <-> valid F.
Proof.
rewrite PCPb_iff_dPCPb.
split.
-
intros [u H] D I rho.
eapply (@drv_val _ I) in H.
unfold F.
cbn in *.
rewrite !impl_sat in *.
cbn in *.
intros.
eapply (H2 (eval rho (enc u))).
eauto.
-
intros H.
Admitted.

Lemma prep_subst sigma t x : subst_term sigma (prep x t) = prep x (subst_term sigma t).
Proof.
Admitted.

Lemma drv_prv (s : peirce) u v : derivable R u v -> ctx_S ⊢ Pr (enc u) (enc v).
Proof.
induction 1.
-
apply Ctx.
right.
eapply in_app_iff.
right.
rewrite <- in_rev.
eapply in_map_iff.
exists (x/y).
eauto.
-
assert (ctx_S ⊢ ∀ ∀ Pr $1 $0 --> Pr (prep x $1) (prep y $0)).
+
apply Ctx.
right.
eapply in_app_iff.
left.
rewrite <- in_rev.
eapply in_map_iff.
exists (x/y).
eauto.
+
eapply AllE with (t := enc u) in H1; eauto.
cbn in H1.
rewrite !prep_subst in H1.
cbn in H1.
eapply AllE with (t := enc v) in H1; eauto.
cbn in H1.
unfold enc in H1.
rewrite !prep_subst in H1.
cbn in H1.
unfold enc.
rewrite !prep_app.
eapply (IE H1).
Admitted.

Lemma BPCP_prv' (s : peirce) : dPCPb R -> [] ⊢ F.
Proof.
intros [u H].
apply drv_prv with (s:=s) in H.
unfold F.
repeat eapply impl_prv.
simpl_list.
eapply II.
assert (ctx_S ⊢ (∀ Pr $0 $0 --> Q)).
apply Ctx.
now unfold ctx_S.
eapply AllE with (t := enc u) in H0.
cbn in H0.
Admitted.

Theorem BPCP_prv R : PCPb R <-> nil ⊢M (F R).
Proof.
rewrite PCPb_iff_dPCPb.
split.
-
apply BPCP_prv'.
-
intros H % soundness'.
eapply PCPb_iff_dPCPb.
Admitted.

Lemma valid_satis phi : valid phi -> ~ satis (¬ phi).
Proof.
intros H1 (D & I & rho & H2).
Admitted.

Theorem BPCP_satis R : ~ PCPb R <-> satis (¬ F R).
Proof.
rewrite PCPb_iff_dPCPb.
split.
-
intros H.
exists (list bool), (IB R), (fun _ => nil).
intros H'.
cbn.
apply H, (IB_F H').
-
rewrite <- PCPb_iff_dPCPb.
intros H1 H2 % (BPCP_valid R (ff:=falsity_on)).
Admitted.

Corollary valid_star_red : PCPb ⪯ FOL*_valid.
Proof.
exists (fun R => F R).
intros R.
Admitted.

Lemma IB_F3 rho : rho ⊨ F3.
Proof.
cbn.
unfold dPCPb, dPCP.
eauto.
