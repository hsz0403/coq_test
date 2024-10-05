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

Theorem prv_red : PCPb ⪯ FOL*_prv_intu.
Proof.
exists (fun R => F R).
intros R.
Admitted.

Corollary valid_red : PCPb ⪯ FOL_valid.
Proof.
exists (fun R => F R).
intros R.
Admitted.

Theorem satis_red : complement PCPb ⪯ FOL_satis.
Proof.
exists (fun R => ¬ F R).
intros R.
Admitted.

Lemma form_discrete {ff : falsity_flag} : discrete (form ff).
Proof.
apply discrete_iff.
constructor.
apply dec_form.
-
intros ? ?.
unfold dec.
repeat decide equality.
-
intros ? ?.
unfold dec.
repeat decide equality.
-
intros [] [].
now left.
-
intros [] [].
Admitted.

Corollary valid_undec : UA -> ~ decidable (@valid _ _ falsity_off).
Proof.
intros H.
Admitted.

Corollary valid_unenum : UA -> ~ enumerable (complement (@valid _ _ falsity_off)).
Proof.
intros H.
Admitted.

Corollary prv_undec : UA -> ~ decidable (@prv _ _ falsity_off intu nil).
Proof.
intros H.
Admitted.

Corollary prv_unenum : UA -> ~ enumerable (complement (@prv _ _ falsity_off intu nil)).
Proof.
intros H.
Admitted.

Corollary satis_undec : UA -> ~ decidable (@satis _ _ falsity_on).
Proof.
intros H1 H2 % (dec_red satis_red).
Admitted.

Corollary satis_enum : UA -> ~ enumerable (@satis _ _ falsity_on).
Proof.
Admitted.

Lemma IB_eval_Some rho t u v : eval rho t = Some v -> eval rho (prep u t) = Some (u ++ v).
Proof.
intros H.
induction u; cbn; trivial.
unfold prep in IHu.
fold prep in IHu.
Admitted.

Lemma IB_eval_None rho t u : eval rho t = None -> eval rho (prep u t) = None.
Proof.
intros H.
induction u; cbn; trivial.
unfold prep in IHu.
fold prep in IHu.
Admitted.

Lemma IB_enc rho u : eval rho (enc u) = Some u.
Proof.
unfold enc.
rewrite <- (app_nil_r u) at 2.
Admitted.

Lemma IB_deriv rho u v : rho ⊨ (Pr (enc u) (enc v)) <-> derivable R u v.
Proof.
cbn.
rewrite !IB_enc.
Admitted.

Lemma IB_deriv' rho t1 t2 u v : eval rho t1 = Some u -> eval rho t2 = Some v -> rho ⊨ (Pr t1 t2) <-> derivable R u v.
Proof.
intros H1 H2.
cbn.
rewrite H1, H2.
Admitted.

Lemma IB_F1 rho : rho ⊫ F1 R.
Proof.
unfold F1.
intros ? ([x y] & <- & ?) % in_map_iff.
cbn.
rewrite !IB_enc.
Admitted.

Lemma IB_F2 rho : rho ⊫ F2 R.
Proof.
unfold F2.
intros ? ([x y] & <- & ?) % in_map_iff [u|] [v|] ?; cbn in *.
-
erewrite !IB_eval_Some; cbn; auto.
now constructor 2.
-
erewrite IB_eval_Some, IB_eval_None; cbn; auto.
-
erewrite IB_eval_None; cbn; auto.
-
Admitted.

Lemma IB_F rho : rho ⊨ F R.
Proof.
unfold F.
rewrite !impl_sat.
intros _ _ H.
apply (H None).
cbn.
Admitted.

Lemma IB_nonstandard rho : rho ⊨ ¬ ∀ ¬ Pr $0 $0.
Proof.
intros H.
apply (H None).
cbn.
Admitted.

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
