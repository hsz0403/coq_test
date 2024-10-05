From Undecidability.L Require Export Prelim.ARS Prelim.MoreBase.
From Undecidability.Shared.Libs.PSL Require Export Base Bijection.
From Undecidability.L Require Export L.
Require Import Lia.
Hint Constructors ARS.star : cbv.
Notation "'#' v" := (var v) (at level 1).
Module L_Notations_app.
Coercion app : term >-> Funclass.
End L_Notations_app.
Module L_Notations.
Coercion var : nat >-> term.
Export L_Notations_app.
End L_Notations.
Instance term_eq_dec : eq_dec term.
Proof.
intros s t; unfold dec; repeat decide equality.
Defined.
Definition term_eq_dec_proc s t := if Dec (s = t) then true else false.
Hint Resolve term_eq_dec : core.
Inductive hoas : Type := hv (n : nat) | ha (s t : hoas) | hl (f : nat -> hoas) | hter (t : term).
Fixpoint TH n s := match s with | hv m => var (n - m - 1) | ha s t => app (TH n s) (TH n t) | hl f => lam (TH (S n) (f n)) | hter t => t end.
Definition convert := TH 0.
Module HOAS_Notations.
Coercion hv : nat >-> hoas.
Coercion ha : hoas >-> Funclass.
Notation "'!!' s" := (hter s) (at level 0).
Notation "[ 'L_HOAS' p ]" := (convert p) (at level 0, format "[ 'L_HOAS' p ]").
Notation "'λ' x .. y , p" := (hl (fun x => .. (hl (fun y => p)) ..)) (at level 100, x binder, right associativity, format "'[' 'λ' '/ ' x .. y , '/ ' p ']'").
End HOAS_Notations.
Arguments convert /.
Import HOAS_Notations.
Definition r := Eval simpl in [L_HOAS λ r f, f (λ x , r r f x) ].
Definition R := app r r.
Definition rho (s : term) := Eval simpl in [L_HOAS λ x, !!r !!r !!s x].
Definition I := Eval simpl in [L_HOAS λ x, x].
Definition K := Eval simpl in [L_HOAS λ x y, x].
Definition omega : term := Eval simpl in [L_HOAS λ x , x x].
Definition Omega : term := app omega omega.
Definition closed s := forall n u, subst s n u = s.
Definition lambda s := exists t, s = lam t.
Definition proc s := closed s /\ lambda s.
Hint Resolve lambda_lam : core.
Instance lambda_dec s : dec (lambda s).
Proof.
destruct s;[right;intros C;inv C;congruence..|left;eexists;eauto].
Defined.
Fixpoint size (t : term) := match t with | var n => 1 + n | app s t => 1+ size s + size t | lam s => 1 + size s end.
Fixpoint size' (t : term) := match t with | var n => 0 | app s t => 1+ size' s + size' t | lam s => 1 + size' s end.
Inductive bound : nat -> term -> Prop := | dclvar k n : k > n -> bound k (var n) | dclApp k s t : bound k s -> bound k t -> bound k (app s t) | dcllam k s : bound (S k) s -> bound k (lam s).
Instance bound_dec k s : dec (bound k s).
Proof with try ((left; econstructor; try lia; tauto) || (right; inversion 1; try lia; tauto)).
revert k; induction s; intros k.
-
destruct (le_lt_dec n k) as [Hl | Hl]...
destruct (le_lt_eq_dec _ _ Hl)...
-
destruct (IHs1 k), (IHs2 k)...
-
induction k.
+
destruct (IHs 1)...
+
destruct (IHs (S (S k)))...
Defined.
Instance closed_dec s : dec (closed s).
Proof.
decide (bound 0 s);[left|right];now rewrite closed_dcl.
Defined.
Reserved Notation "s '≻' t" (at level 50).
Inductive step : term -> term -> Prop := | stepApp s t : app (lam s) (lam t) ≻ subst s 0 (lam t) | stepAppR s t t' : t ≻ t' -> app s t ≻ app s t' | stepAppL s s' t : s ≻ s' -> app s t ≻ app s' t where "s '≻' t" := (step s t).
Hint Constructors step : core.
Ltac inv_step := match goal with | H : step (lam _) _ |- _ => inv H | H : step (var _) _ |- _ => inv H | H : star step (lam _) _ |- _ => inv H | H : star step (var _) _ |- _ => inv H end.
Goal forall s, closed s -> ((~ exists t, s ≻ t) <-> proc s).
Proof.
intros s cls_s.
split.
destruct (comb_proc_red cls_s).
-
eauto.
-
tauto.
-
destruct 1 as [? [? ?]].
subst.
destruct 1 as [? B].
inv B.
Notation "s '>(' l ')' t" := (pow step l s t) (at level 50, format "s '>(' l ')' t").
Arguments pow: simpl never.
Notation "s '>*' t" := (star step s t) (at level 50).
Instance star_PreOrder : PreOrder (star step).
Proof.
constructor; hnf.
-
eapply starR.
-
eapply star_trans.
Instance step_star_subrelation : subrelation step (star step).
Proof.
cbv.
apply step_star.
Instance star_step_app_proper : Proper ((star step) ==> (star step) ==> (star step)) app.
Proof.
cbv.
intros s s' A t t' B.
etransitivity.
apply (star_trans_l _ A).
now apply star_trans_r.
Instance star_closed_proper : Proper ((star step) ==> Basics.impl) closed.
Proof.
exact closed_star.
Instance pow_step_congL k: Proper ((pow step k) ==> eq ==> (pow step k)) app.
Proof.
intros s t R u ? <-.
revert s t R u.
induction k;cbn in *;intros ? ? R ?.
congruence.
destruct R as [s' [R1 R2]].
exists (app s' u).
firstorder.
Instance pow_step_congR k: Proper (eq ==>(pow step k) ==> (pow step k)) app.
Proof.
intros s ? <- t u R.
revert s t u R.
induction k;cbn in *;intros ? ? ? R.
congruence.
destruct R as [t' [R1 R2]].
exists (app s t').
firstorder.
Reserved Notation "s '==' t" (at level 50).
Inductive equiv : term -> term -> Prop := | eqStep s t : step s t -> s == t | eqRef s : s == s | eqSym s t : t == s -> s == t | eqTrans s t u: s == t -> t == u -> s == u where "s '==' t" := (equiv s t).
Hint Immediate eqRef : core.
Instance equiv_Equivalence : Equivalence equiv.
Proof.
constructor; hnf.
-
apply eqRef.
-
intros.
eapply eqSym.
eassumption.
-
apply eqTrans.
Hint Resolve star_equiv : core.
Instance star_equiv_subrelation : subrelation (star step) equiv.
Proof.
cbv.
apply star_equiv.
Instance step_equiv_subrelation : subrelation step equiv.
Proof.
cbv.
intros ? ? H.
apply star_equiv, step_star.
assumption.
Instance equiv_app_proper : Proper (equiv ==> equiv ==> equiv) app.
Proof.
cbv.
intros s s' A t t' B.
eapply eqApp; eassumption.
Definition converges s := exists t, s == t /\ lambda t.
Instance converges_proper : Proper (equiv ==> iff) converges.
Proof.
intros s t H.
now eapply converges_equiv.
Instance pow_star_subrelation i: subrelation (pow step i) (star step).
Proof.
intros ? ? ?.
eapply pow_star;eauto.
Definition eval s t := s >* t /\ lambda t.
Notation "s '⇓' t" := (eval s t) (at level 51).
Hint Unfold eval : core.
Instance eval_star_subrelation : subrelation eval (star step).
Proof.
now intros ? ? [].
Instance reduce_eval_proper : Proper (Basics.flip (star step) ==> eq ==> Basics.impl) eval.
Proof.
repeat intro.
subst.
unfold Basics.flip in H.
destruct H1.
split.
etransitivity.
eassumption.
assumption.
assumption.
Instance equiv_eval_proper: Proper (equiv ==> eq ==> Basics.impl) eval.
Proof.
repeat intro;subst.
destruct H1.
split;try auto.
apply equiv_lambda.
auto.
now rewrite <- H0, H.
Definition evalIn i s t := s >(i) t /\ lambda t.
Notation "s '⇓(' l ')' t" := (evalIn l s t) (at level 50, format "s '⇓(' l ')' t").
Definition redLe l s t := exists i , i <= l /\ pow step i s t.
Notation "s '>(<=' l ')' t" := (redLe l s t) (at level 50, format "s '>(<=' l ')' t").
Definition evalLe l s t := s >(<=l) t /\ lambda t.
Notation "s '⇓(<=' l ')' t" := (evalLe l s t) (at level 50, format "s '⇓(<=' l ')' t").
Instance evalLe_eval_subrelation i: subrelation (evalLe i) eval.
Proof.
intros ? ? [[? []] ?].
split.
eapply pow_star_subrelation.
all:eauto.
Instance evalIn_evalLe_subrelation i: subrelation (evalIn i) (evalLe i).
Proof.
intros s t (R & lt).
split;[now exists i|trivial].
Instance pow_redLe_subrelation i: subrelation (pow step i) (redLe i).
Proof.
intros s t R.
now exists i.
Instance evalLe_redLe_subrelation i: subrelation (evalLe i) (redLe i).
Proof.
now intros ? ? [].
Instance evalIn_eval_subrelation i: subrelation (evalIn i) eval.
Proof.
intros ? ? [? ?].
split.
eapply pow_star_subrelation.
all:eauto.
Instance redLe_star_subrelation i: subrelation (redLe i) (star step).
Proof.
intros ? ? (j & leq & R).
now rewrite R.
Instance le_redLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) redLe.
Proof.
intros ? ? ? ? ? -> ? ? -> (i&lt&R).
exists i.
split.
lia.
tauto.
Instance le_evalLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) evalLe.
Proof.
intros ? ? H' ? ? -> ? ? -> [H p].
split.
2:tauto.
now rewrite <- H'.
Instance pow0_refl : Reflexive (pow step 0).
Proof.
intro.
reflexivity.
Instance redLe_refl : Reflexive (redLe 0).
Proof.
intro.
eexists; split;reflexivity.

Lemma evalLe_evalIn s t k: s ⇓(<=k) t -> exists k', k' <= k /\ s ⇓(k') t.
Proof.
unfold evalLe,redLe,evalIn.
Admitted.

Lemma evalIn_evalLe s t k k': k' <= k -> s ⇓(k') t -> s ⇓(<=k) t.
Proof.
unfold evalLe,redLe,evalIn.
Admitted.

Instance evalIn_evalLe_subrelation i: subrelation (evalIn i) (evalLe i).
Proof.
intros s t (R & lt).
Admitted.

Instance pow_redLe_subrelation i: subrelation (pow step i) (redLe i).
Proof.
intros s t R.
Admitted.

Instance evalLe_redLe_subrelation i: subrelation (evalLe i) (redLe i).
Proof.
Admitted.

Instance evalIn_eval_subrelation i: subrelation (evalIn i) eval.
Proof.
intros ? ? [? ?].
split.
eapply pow_star_subrelation.
Admitted.

Instance redLe_star_subrelation i: subrelation (redLe i) (star step).
Proof.
intros ? ? (j & leq & R).
Admitted.

Instance le_redLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) redLe.
Proof.
intros ? ? ? ? ? -> ? ? -> (i&lt&R).
exists i.
split.
lia.
Admitted.

Lemma redLe_mono s t n n' : s >(<=n) t -> n <= n' -> s >(<=n') t.
Proof.
intros ? <-.
Admitted.

Instance le_evalLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) evalLe.
Proof.
intros ? ? H' ? ? -> ? ? -> [H p].
split.
2:tauto.
Admitted.

Lemma evalIn_mono s t n n' : s ⇓(<=n) t -> n <= n' -> s ⇓(<=n') t.
Proof.
intros ? <-.
Admitted.

Lemma evalIn_trans s t u i j : s >(i) t -> t ⇓(j) u -> s ⇓(i+j) u.
Proof.
intros R1 [R2 lam].
Admitted.

Lemma redLe_trans s t u i j : s >(<=i) t -> t >(<=j) u -> s >(<=i+j) u.
Proof.
intros [i' [? R1]] [j' [? R2]].
exists (i'+j').
split.
lia.
apply pow_add.
Admitted.

Lemma redLe_trans_eq s t u i j k : i+j=k -> s >(<=i) t -> t >(<=j) u -> s >(<=k) u.
Proof.
Admitted.

Lemma evalLe_trans s t u i j : s >(<=i) t -> t ⇓(<=j) u -> s ⇓(<=i+j) u.
Proof.
intros R1 [R2 lam].
Admitted.

Instance pow0_refl : Reflexive (pow step 0).
Proof.
intro.
Admitted.

Instance redLe_refl : Reflexive (redLe 0).
Proof.
intro.
Admitted.

Lemma evalIn_unique s k1 k2 v1 v2 : s ⇓(k1) v1 -> s ⇓(k2) v2 -> k1 = k2 /\ v1 = v2.
Proof.
intros (R1&L1) (R2&L2).
eapply uniform_confluence_parameterized_both_terminal.
Admitted.

Lemma eval_evalIn s t: eval s t -> exists k, evalIn k s t.
Proof.
intros [(R&?)%star_pow ?].
unfold evalIn.
Admitted.

Lemma pow_trans_lam' t v s k j: lambda v -> pow step j t v -> pow step k t s -> j>=k /\ pow step (j-k) s v.
Proof.
intros lv A B.
destruct (parametrized_confluence uniform_confluence A B) as [m' [l [u [m_le_Sk [l_le_n [C [D E]]]]]]].
cut (m' = 0).
-
intros ->.
split.
lia.
replace (j-k) with l by lia.
hnf in C.
subst v.
tauto.
-
destruct m'; eauto.
destruct C.
destruct H.
inv lv.
Admitted.

Lemma pow_trans_lam t v s k n : lambda v -> pow step n t v -> pow step (S k) t s -> exists m, m < n /\ pow step m s v.
Proof.
intros H1 H2 H3.
edestruct (pow_trans_lam' H1 H2 H3) as (H'1&H'2).
do 2 eexists.
2:eassumption.
Admitted.

Lemma powSk t t' s : t ≻ t' -> t' >* s -> exists k, pow step (S k) t s.
Proof.
intros A B.
eapply star_pow in B.
destruct B as [n B].
exists n.
unfold pow.
simpl.
econstructor.
unfold pow in B.
Admitted.

Lemma rho_dcls n s : bound (S n) s -> bound n (rho s).
Proof.
unfold rho,r.
intros H.
Admitted.

Lemma closed_dcl_x x s: closed s -> bound x s.
Proof.
intros.
apply (@bound_ge 0).
now apply closed_dcl.
Admitted.

Lemma rho_cls s : closed s -> closed (rho s).
Proof.
intros.
rewrite closed_dcl.
apply rho_dcls.
Admitted.

Lemma rho_lambda s : lambda (rho s).
Proof.
eexists.
Admitted.

Lemma step_eval s t v : s ≻ t -> L.eval t v -> L.eval s v.
Proof.
induction 1 in v |- *; intros He.
-
repeat econstructor; eauto.
-
inv He.
econstructor; eauto.
-
inv He.
Admitted.

Lemma eval_iff s t : L.eval s t <-> s ⇓ t.
Proof.
split.
-
induction 1.
+
split.
reflexivity.
eauto.
+
split.
destruct IHeval2 as [IH1 [v' ->]].
2:eapply IHeval3.
rewrite IHeval1, IH1.
econstructor.
2:eapply IHeval3.
econstructor.
-
intros [H1 [v ->]].
revert H1.
revert s.
eapply (star_simpl_ind (y := lam v)).
+
econstructor.
+
intros s s' H1 H2 IH.
Admitted.

Lemma evalLe_trans_rev t v s k j: evalLe j t v -> pow step k t s -> j>=k /\ evalLe (j-k) s v.
Proof.
intros [(i&lti&R) lv] B.
edestruct (pow_trans_lam' lv R B).
split.
lia.
split.
2:tauto.
eexists;split.
2:eauto.
lia.
