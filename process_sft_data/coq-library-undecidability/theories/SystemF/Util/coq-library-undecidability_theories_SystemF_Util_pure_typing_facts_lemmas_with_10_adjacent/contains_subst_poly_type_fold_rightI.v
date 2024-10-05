Require Import List Lia Relation_Definitions Relation_Operators Operators_Properties.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts iipc2_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments funcomp {X Y Z} _ _ / _.
Arguments fresh_in _ _ /.
Inductive contains_step : poly_type -> poly_type -> Prop := | contains_step_subst {s t} : contains_step (poly_abs t) (subst_poly_type (scons s poly_var) t).
Definition contains := clos_refl_trans poly_type contains_step.
Inductive pure_typing : environment -> pure_term -> poly_type -> Prop := | pure_typing_pure_var n {Gamma x t t'} : nth_error (map (ren_poly_type (Nat.add n)) Gamma) x = Some t -> contains t t' -> pure_typing Gamma (pure_var x) (many_poly_abs n t') | pure_typing_pure_app n {Gamma M N s t t'} : pure_typing (map (ren_poly_type (Nat.add n)) Gamma) M (poly_arr s t) -> pure_typing (map (ren_poly_type (Nat.add n)) Gamma) N s -> contains t t' -> pure_typing Gamma (pure_app M N) (many_poly_abs n t') | pure_typing_pure_abs n {Gamma M s t} : pure_typing (s :: map (ren_poly_type (Nat.add n)) (Gamma)) M t -> pure_typing Gamma (pure_abs M) (many_poly_abs n (poly_arr s t)).
Definition pure_typable Gamma M := exists t, pure_typing Gamma M t.
Arguments pure_typable : simpl never.
Fixpoint tidy (t: poly_type) := match t with | poly_var _ => t | poly_arr s t => poly_arr (tidy s) (tidy t) | poly_abs t => if fresh_inb 0 t then ren_poly_type (scons 0 id) (tidy t) else (poly_abs (tidy t)) end.

Lemma typing_tidyI {Gamma P t} : typing Gamma P t -> exists Q, erase P = erase Q /\ typing (map tidy Gamma) Q (tidy t).
Proof.
elim: P Gamma t.
-
move=> x Gamma t /typingE Hx.
exists (var x).
constructor; first done.
apply: typing_var.
by rewrite nth_error_map Hx.
-
move=> P IHP Q IHQ Gamma t /typingE [?] /= [/IHP [P'] [->] {}IHP /IHQ [Q'] [->] {}IHQ].
exists (app P' Q').
constructor; first done.
apply: typing_app; by eassumption.
-
move=> s P IH Gamma t /typingE [?] /= [->] /IH [P'] [->] HP'.
exists (abs (tidy s) P').
constructor; first done.
by apply: typing_abs.
-
move=> P IH s Gamma t /typingE [t'] /= [->] /IH [P'] [->].
move=> /typing_contains.
apply.
by apply /contains_tidyI /rt_step /contains_step_subst.
-
move=> P IH Gamma t /typingE [t'] /= [->] /IH [P'] [->] /=.
case Hb: (fresh_inb _ _).
+
move=> /(typing_ren_poly_type (0 .: id)) => H.
exists (ren_term (0 .: id) id P').
constructor; first by rewrite erase_ren_term_id.
congr typing: H.
rewrite ?map_map.
apply: map_ext => ?.
by rewrite tidy_ren_poly_type ?poly_type_norm /= ren_poly_type_id.
+
move=> H.
exists (ty_abs P').
constructor; first done.
apply: typing_ty_abs.
congr typing: H.
rewrite ?map_map.
apply: map_ext => ?.
Admitted.

Lemma pure_typing_tidyI {Gamma M t} : pure_typing Gamma M t -> pure_typing (map tidy Gamma) M (tidy t).
Proof.
Admitted.

Lemma tidy_tidy {t} : tidy (tidy t) = tidy t.
Proof.
elim: t; [done | by move=> /= ? -> ? -> |].
move=> t /=.
case Ht: (fresh_inb _ _).
-
by rewrite ?tidy_ren_poly_type => ->.
-
rewrite /=.
have -> : fresh_inb 0 (tidy t) = fresh_inb 0 t.
{
apply /is_trueP.
by rewrite -?(rwP fresh_inP) /= allfv_poly_type_tidy.
}
Admitted.

Lemma tidy_many_poly_abs_tidy {n t} : tidy (many_poly_abs n (tidy t)) = tidy (many_poly_abs n t).
Proof.
elim: n; first by rewrite tidy_tidy.
move=> n /= ->.
have ->: fresh_inb 0 (many_poly_abs n (tidy t)) = fresh_inb 0 (many_poly_abs n t).
{
apply /is_trueP.
by rewrite -?(rwP fresh_inP) /= ?allfv_poly_type_many_poly_abs allfv_poly_type_tidy.
}
Admitted.

Lemma tidy_many_poly_abs_le {n t}: allfv_poly_type (le n) t -> tidy (many_poly_abs n t) = ren_poly_type (fun x => x - n) (tidy t).
Proof.
elim: n t.
-
move=> t _ /=.
rewrite ren_poly_type_id'; by [|lia].
-
move=> n IH t /= Ht.
have ->: fresh_inb 0 (many_poly_abs n t) = true.
{
apply /fresh_inP.
rewrite /fresh_in allfv_poly_type_many_poly_abs.
apply: allfv_poly_type_impl Ht.
move=> x ?.
rewrite iter_scons_ge; by lia.
}
rewrite IH.
{
apply: allfv_poly_type_impl Ht.
by lia.
}
rewrite poly_type_norm.
apply: extRen_poly_type.
move=> x /=.
Admitted.

Lemma tidy_many_poly_abs {n s} : { n'ξ' | tidy (many_poly_abs n s) = many_poly_abs (n'ξ'.1) (tidy (ren_poly_type (n'ξ'.2) s)) }.
Proof.
elim: n s.
-
move=> s.
exists (0, id).
by rewrite ren_poly_type_id.
-
move=> n IH s /=.
case Hns: (fresh_inb 0 (many_poly_abs n s)).
+
have := IH s.
move=> [[n' ξ']] ->.
rewrite ren_poly_type_many_poly_abs -tidy_ren_poly_type ?poly_type_norm.
evar (n'': nat).
evar (ξ'': nat -> nat).
exists (n'', ξ'') => /=.
by subst n'' ξ''.
+
have := IH s.
move=> [[n' ξ']] ->.
Admitted.

Lemma contains_many_poly_absE {n s1 t1 t} : contains (many_poly_abs n (poly_arr s1 t1)) t -> exists ts, length ts <= n /\ t = subst_poly_type (fold_right scons poly_var ts) (many_poly_abs (n - length ts) (poly_arr s1 t1)).
Proof.
move=> /clos_rt_rtn1_iff.
elim.
-
exists [] => /=.
constructor; first by lia.
by rewrite (ltac:(lia) : n - 0 = n) subst_poly_type_poly_var.
-
move=> > [] r ? _ [ts] [?].
move Hn': (n - length ts) => n'.
case: n' Hn'; first done.
move=> n' ? [->].
exists (r :: ts) => /=.
constructor; first by lia.
have ->: n - S (length ts) = n' by lia.
rewrite ?poly_type_norm.
apply: ext_poly_type.
case; first done.
move=> x /=.
Admitted.

Lemma contains_poly_arrE {n s1 t1 s2 t2} : contains (many_poly_abs n (poly_arr s1 t1)) (poly_arr s2 t2) -> exists ts, n = length ts /\ (poly_arr s2 t2) = subst_poly_type (fold_right scons poly_var ts) (poly_arr s1 t1).
Proof.
move=> /contains_many_poly_absE [ts] [?] H.
have Hnts : n - length ts = 0 by case: (n - length ts) H.
exists ts.
Admitted.

Lemma contains_poly_varE {t x} : contains t (poly_var x) -> exists n y, t = many_poly_abs n (poly_var y).
Proof.
have [n [t' [->]]] := many_poly_absI t.
case: t'.
-
move=> *.
by do 2 eexists.
-
move=> > _ /contains_many_poly_absE [ts] [_].
by case: (n - length ts).
-
Admitted.

Lemma contains_many_poly_abs_free {n x t} : contains (many_poly_abs n (poly_var (n + x))) t -> exists i m, n = i + m /\ t = many_poly_abs m (poly_var (m+x)).
Proof.
elim: n x t.
-
move=> /= x ? /containsE <-.
by exists 0, 0.
-
move=> n IH x t /containsE /= [].
+
move=> <-.
by exists 0, (1+n).
+
move=> [?].
rewrite subst_poly_type_many_poly_abs /=.
have ->: S (n + x) = n + S x by lia.
rewrite iter_up_poly_type_poly_type /=.
move=> /IH [i] [m] [-> ->].
Admitted.

Lemma contains_subst_poly_type_fold_rightE {ts t t'} : contains (subst_poly_type (fold_right scons poly_var ts) t) t' -> contains (many_poly_abs (length ts) t) t'.
Proof.
move Hs: (subst_poly_type (fold_right scons poly_var ts) t) => s /clos_rt_rtn1_iff Hst'.
elim: Hst' t ts Hs.
-
move=> ? ? <-.
by apply: contains_subst_poly_type_fold_rightI.
-
move=> > [] r ? _ IH t ts /IH {}IH.
apply: rt_trans; first by eassumption.
Admitted.

Lemma contains_many_poly_abs_closedI {n s σ} : allfv_poly_type (gt n) s -> contains (many_poly_abs n s) (subst_poly_type σ s).
Proof.
move=> Hns.
pose ts := (map σ (seq 0 n)).
have -> : n = length ts by rewrite /ts map_length seq_length.
apply: contains_subst_poly_type_fold_rightE.
have ->: subst_poly_type (fold_right scons poly_var ts) s = subst_poly_type σ s.
{
apply: ext_subst_poly_type_allfv_poly_type.
apply: allfv_poly_type_impl Hns => x ?.
rewrite /ts fold_right_length_ts_lt; first by (rewrite map_length seq_length; lia).
rewrite [nth _ _ (poly_var 0)](nth_indep _ _ (σ 0)); first by (rewrite map_length seq_length; lia).
rewrite map_nth seq_nth; by [|lia].
}
Admitted.

Lemma pure_typing_ren_pure_term {Gamma Delta M t} (ξ : nat -> nat) : pure_typing Gamma M t -> (forall n s, nth_error Gamma n = Some s -> nth_error Delta (ξ n) = Some s) -> pure_typing Delta (ren_pure_term ξ M) t.
Proof.
move=> /pure_typing_to_typing [P] [->] /typing_ren_term H /H{H} /typing_to_pure_typing.
Admitted.

Lemma pure_typing_ren_pure_term_allfv_pure_term {Gamma Delta M t} (ξ : nat -> nat) : (allfv_pure_term (fun x => nth_error Gamma x = nth_error Delta (ξ x)) M) -> pure_typing Gamma M t -> pure_typing Delta (ren_pure_term ξ M) t.
Proof.
move=> + /pure_typing_to_typing [P] [?].
subst M.
move=> /allfv_pure_term_erase /typing_ren_allfv_term H /H /typing_to_pure_typing.
Admitted.

Lemma pure_typing_many_poly_abs_closed {s t n} : allfv_poly_type (fun=> False) s -> pure_typing [s] (pure_var 0) t -> pure_typing [s] (pure_var 0) (many_poly_abs n t).
Proof.
move=> Hs /pure_typingE [n1] [?] [?] [[?]] [HC ?].
subst.
rewrite many_poly_abs_many_poly_abs.
apply: pure_typing_pure_var; first by reflexivity.
congr contains: HC.
apply: ext_ren_poly_type_allfv_poly_type.
Admitted.

Lemma pure_typing_many_poly_abs_contains_closed {s t t' n} : allfv_poly_type (fun=> False) s -> contains (many_poly_abs n t) t' -> pure_typing [s] (pure_var 0) t -> pure_typing [s] (pure_var 0) t'.
Proof.
Admitted.

Lemma pure_typing_tidy_many_poly_abs_closed {s t n} : allfv_poly_type (fun=> False) s -> pure_typing [s] (pure_var 0) (tidy t) -> pure_typing [tidy s] (pure_var 0) (tidy (many_poly_abs n t)).
Proof.
move=> Hs Ht.
rewrite -tidy_many_poly_abs_tidy -/(map tidy [s]).
apply: pure_typing_tidyI.
Admitted.

Lemma pure_typing_many_poly_abs_contains_tidy_closed {s t t' n} : allfv_poly_type (fun=> False) s -> contains (many_poly_abs n t) t' -> pure_typing [s] (pure_var 0) (tidy t) -> pure_typing [tidy s] (pure_var 0) (tidy t').
Proof.
move=> Hs /contains_tidyI HC /(pure_typing_tidy_many_poly_abs_closed Hs (n := n)) /pure_typing_contains.
Admitted.

Lemma pure_typing_weaken_closed {s s' Gamma1 Gamma2 M t} : allfv_poly_type (fun=> False) s -> pure_typing [s] (pure_var 0) s' -> pure_typing (Gamma1 ++ s' :: Gamma2) M t -> pure_typing (Gamma1 ++ s :: Gamma2) M t.
Proof.
move=> Hs Hss' /pure_typing_to_typing [P] [->].
elim: P Gamma1 Gamma2 s' t Hss'.
-
move=> x Gamma1 Gamma2 s' t Hss' /typingE Hx.
have [?|[H'x|?]] : x < length Gamma1 \/ x - length Gamma1 = 1 + (x - length Gamma1 - 1) \/ length Gamma1 = x by lia.
+
apply: pure_typing_pure_var_simpleI.
move: Hx.
by rewrite ?nth_error_app1.
+
apply: pure_typing_pure_var_simpleI.
move: Hx.
rewrite nth_error_app2; first by lia.
rewrite nth_error_app2; [by lia | by rewrite H'x].
+
move: Hx.
rewrite nth_error_app2; first by lia.
have H'x: x - length Gamma1 = 0 by lia.
move: (H'x) => -> [<-].
move: Hss' => /(pure_typing_ren_pure_term_allfv_pure_term (fun y => y + x)).
apply.
rewrite /= nth_error_app2; first by lia.
by rewrite H'x.
-
move=> ? IH1 ? IH2 > /copy [/IH1 {}IH1 /IH2 {}IH2] /typingE [?] [/IH1 + /IH2 +].
by move=> /pure_typing_pure_app_simpleI H /H.
-
move=> ? ? IH > /IH {}IH /typingE [?] [->].
rewrite -/((_ :: _) ++ _).
by move=> /IH /= /pure_typing_pure_abs_simpleI.
-
move=> > IH > /IH {}IH /typingE [?] [->] /IH.
apply: pure_typing_contains.
by apply /rt_step /contains_step_subst.
-
move=> > IH > Hss' /typingE [?] [->].
rewrite map_app /=.
move=> /IH.
apply: unnest.
{
move: Hss' => /(pure_typing_ren_poly_type S).
congr pure_typing => /=.
by rewrite ren_poly_type_closed_id.
}
move=> {}IH.
apply: (pure_typing_many_poly_absI (n := 1)).
congr pure_typing: IH.
Admitted.

Lemma tidy_is_simple {t} : is_simple t -> tidy t = t.
Proof.
Admitted.

Lemma contains_subst_poly_type_fold_rightI {ts t} : contains (many_poly_abs (length ts) t) (subst_poly_type (fold_right scons poly_var ts) t).
Proof.
elim: ts t.
-
move=> /= ?.
rewrite subst_poly_type_poly_var.
by apply: rt_refl.
-
move=> r ts IH t.
rewrite [length _]/=.
have ->: S (length ts) = (length ts) + 1 by lia.
rewrite -many_poly_abs_many_poly_abs /=.
have {}IH := IH (poly_abs t).
apply: rt_trans; first by eassumption.
apply: rt_step => /=.
have := contains_step_subst.
evar (s': poly_type) => /(_ s').
evar (t': poly_type) => /(_ t').
congr contains_step.
subst t'.
rewrite ?poly_type_norm /=.
apply: ext_poly_type.
case=> /=; first by subst s'.
move=> ?.
by rewrite poly_type_norm /= subst_poly_type_poly_var.
