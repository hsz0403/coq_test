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

Lemma pure_typing_pure_var_simpleI {Gamma x t} : nth_error Gamma x = Some t -> pure_typing Gamma (pure_var x) t.
Proof.
move=> Hx.
apply: (pure_typing_pure_var 0); last by apply: rt_refl.
rewrite nth_error_map Hx /=.
Admitted.

Lemma pure_typing_pure_app_simpleI {Gamma M N s t} : pure_typing Gamma M (poly_arr s t) -> pure_typing Gamma N s -> pure_typing Gamma (pure_app M N) t.
Proof.
move=> HM HN.
apply: (pure_typing_pure_app 0 (s := s)); last by apply: rt_refl.
-
by rewrite map_ren_poly_type_id.
-
Admitted.

Lemma pure_typing_pure_abs_simpleI {Gamma M s t} : pure_typing (s :: Gamma) M t -> pure_typing Gamma (pure_abs M) (poly_arr s t).
Proof.
move=> HM.
apply: (pure_typing_pure_abs 0).
Admitted.

Lemma pure_typing_many_poly_absI {n Gamma M t} : pure_typing (map (ren_poly_type (Nat.add n)) Gamma) M t -> pure_typing Gamma M (many_poly_abs n t).
Proof.
have Hnn' : forall Gamma n n', (map (ren_poly_type (Nat.add n')) (map (ren_poly_type (Nat.add n)) Gamma)) = map (ren_poly_type (Nat.add (n + n'))) Gamma.
{
move=> *.
rewrite ?map_map.
apply: map_ext => ?.
rewrite poly_type_norm /=.
apply: extRen_poly_type.
by lia.
}
case: M.
-
move=> x /pure_typingE [n'] [?] [?] [+] [HC] ->.
rewrite Hnn' many_poly_abs_many_poly_abs => ?.
apply: (pure_typing_pure_var (n + n')); by eassumption.
-
move=> ? ? /pure_typingE [n'] [?] [?] [?] [+] [+] [HC] ->.
rewrite ?Hnn' many_poly_abs_many_poly_abs => ? ?.
apply: (pure_typing_pure_app (n + n')); by eassumption.
-
move=> ? /pure_typingE [n'] [?] [?] [+] ->.
rewrite ?Hnn' many_poly_abs_many_poly_abs => ?.
Admitted.

Lemma pure_typing_subst_poly_type {Gamma M t} σ : pure_typing Gamma M t -> pure_typing (map (subst_poly_type σ) Gamma) M (subst_poly_type σ t).
Proof.
pose σ' n σ := Nat.iter n up_poly_type_poly_type σ.
have Hσ' : forall n t σ, subst_poly_type (σ' n σ) (ren_poly_type (Nat.add n) t) = ren_poly_type (Nat.add n) (subst_poly_type σ t).
{
move=> >.
rewrite ?poly_type_norm /σ' /=.
apply: ext_poly_type.
move=> ?.
by rewrite iter_up_poly_type_poly_type.
}
move=> H.
elim: H σ.
-
move=> n {}Gamma x > Hx + σ => /(contains_subst_poly_typeI (σ' n σ)) HC.
rewrite subst_poly_type_many_poly_abs.
apply: (pure_typing_pure_var n); last by eassumption.
move: Hx.
rewrite ?nth_error_map.
case: (nth_error Gamma x); last done.
move=> ? [<-] /=.
by rewrite Hσ'.
-
move=> n > _ + _ + + σ => /(_ (σ' n σ)) + /(_ (σ' n σ)) + /(contains_subst_poly_typeI (σ' n σ)) ?.
rewrite ?map_map.
under map_ext => ? do rewrite Hσ'.
move=> ? ?.
rewrite subst_poly_type_many_poly_abs.
apply: (pure_typing_pure_app n); rewrite ?map_map; by eassumption.
-
move=> n > _ + σ => /(_ (σ' n σ)).
rewrite /= map_map.
under map_ext => ? do rewrite Hσ'.
move=> ?.
rewrite subst_poly_type_many_poly_abs /=.
apply: (pure_typing_pure_abs n).
rewrite ?map_map.
Admitted.

Lemma pure_typing_poly_absE {s Gamma M t} : pure_typing Gamma M (poly_abs t) -> pure_typing Gamma M (subst_poly_type (s .: poly_var) t).
Proof.
pose σ n s := Nat.iter n up_poly_type_poly_type (s .: poly_var).
have Hσ: forall n t s, subst_poly_type (σ n s) (ren_poly_type (Nat.add (S n)) t) = ren_poly_type (Nat.add n) t.
{
move=> n >.
rewrite ?poly_type_norm [RHS]ren_as_subst_poly_type /σ.
apply: ext_poly_type => y /=.
rewrite iter_up_poly_type_poly_type_ge; first by lia.
by have ->: S (n + y) - n = S y by lia.
}
elim: M s Gamma t.
-
move=> x s Gamma t /pure_typingE [[|n]] [tx] [?] [+] [+] /=.
+
move=> *.
subst.
apply: (pure_typing_pure_var 0); first by eassumption.
apply: rt_trans; [by eassumption | by apply /rt_step /contains_step_subst].
+
move=> Hx /(contains_subst_poly_typeI (σ n s)) HC [?].
subst.
rewrite subst_poly_type_many_poly_abs.
apply: (pure_typing_pure_var n); last by eassumption.
move: Hx.
rewrite ?nth_error_map.
case: (nth_error Gamma x); last done.
move=> ? /= [<-].
by rewrite Hσ.
-
move=> ? IH1 ? IH2 s Gamma t /pure_typingE [[|n]] [?] [?] [?] [+] [+] [].
+
move=> ? ? ? /= ?.
subst.
apply: (pure_typing_pure_app 0); [by eassumption | by eassumption |].
apply: rt_trans; [by eassumption | by apply /rt_step /contains_step_subst].
+
move=> /(pure_typing_subst_poly_type (σ n s)) /= + /(pure_typing_subst_poly_type (σ n s)) /= +.
rewrite ?map_map.
under map_ext => ? do rewrite Hσ.
move=> ? ?.
move=> /(contains_subst_poly_typeI (σ n s)) ? [->].
rewrite subst_poly_type_many_poly_abs.
apply: (pure_typing_pure_app n); by eassumption.
-
move=> ? IH s Gamma t /pure_typingE [[|n]] [?] [?] []; first done.
move=> + [->].
rewrite subst_poly_type_many_poly_abs.
move=> /(pure_typing_subst_poly_type (σ n s)) /=.
rewrite ?map_map.
under map_ext => ? do rewrite Hσ.
move=> ?.
Admitted.

Theorem typing_to_pure_typing {Gamma P t} : typing Gamma P t -> pure_typing Gamma (erase P) t.
Proof.
elim => *.
-
by apply: pure_typing_pure_var_simpleI.
-
apply: pure_typing_pure_app_simpleI; by eassumption.
-
by apply: pure_typing_pure_abs_simpleI.
-
by apply: pure_typing_poly_absE.
-
Admitted.

Theorem pure_typing_to_typing {Gamma M t} : pure_typing Gamma M t -> exists P, M = erase P /\ typing Gamma P t.
Proof.
elim.
-
move=> > /typing_var /typing_contains H /H {H} [?] /= [->] /typing_many_ty_absI ?.
eexists.
constructor; last by eassumption.
by rewrite erase_many_ty_abs.
-
move=> > _ [P] [-> +] _ [Q] [-> +] => /typing_app H /H /typing_contains {}H /H.
move=> [?] /= [->] /typing_many_ty_absI ?.
eexists.
constructor; last by eassumption.
by rewrite erase_many_ty_abs.
-
move=> > _ [?] [->] /typing_abs /typing_many_ty_absI ?.
eexists.
constructor; last by eassumption.
Admitted.

Lemma pure_typing_contains {s t Gamma M} : contains s t -> pure_typing Gamma M s -> pure_typing Gamma M t.
Proof.
Admitted.

Lemma pure_typing_ren_poly_type {Gamma M t} ξ : pure_typing Gamma M t -> pure_typing (map (ren_poly_type ξ) Gamma) M (ren_poly_type ξ t).
Proof.
move=> /pure_typing_to_typing [?] [->] /(typing_ren_poly_type ξ) /typing_to_pure_typing.
congr pure_typing.
Admitted.

Lemma pure_typing_many_poly_absE {n Gamma M t} : pure_typing Gamma M (many_poly_abs n t) -> pure_typing (map (ren_poly_type (Nat.add n)) Gamma) M t.
Proof.
elim: n Gamma t.
-
move=> > /=.
by rewrite map_ren_poly_type_id.
-
move=> n IH Gamma t /=.
move=> /(pure_typing_ren_poly_type S) /pure_typing_to_typing [?] [?] /=.
move=> /typing_ty_app => /(_ (poly_var 0)).
subst M.
rewrite ?poly_type_norm subst_poly_type_poly_var'; first by case.
move=> /typing_to_pure_typing /= /IH.
congr pure_typing.
rewrite ?map_map.
apply: map_ext => ?.
rewrite ?poly_type_norm /=.
apply: extRen_poly_type.
Admitted.

Lemma allfv_poly_type_tidy {P t} : allfv_poly_type P (tidy t) <-> allfv_poly_type P t.
Proof.
elim: t P; [done | by move=> /= ? + ? + ? => -> -> |].
move=> ? IH ? /=.
case H: (fresh_inb _ _); last by apply: IH.
rewrite allfv_poly_type_ren_poly_type IH.
apply: ext_allfv_poly_type_allfv_poly_type.
move: H => /(fresh_inP).
apply: allfv_poly_type_impl.
Admitted.

Lemma tidy_ren_poly_type {ξ t} : tidy (ren_poly_type ξ t) = ren_poly_type ξ (tidy t).
Proof.
elim: t ξ; [done | by move=> ? + ? + ? /= => -> -> |].
move=> ? IH ξ /=.
set b1 := (fresh_inb _ (ren_poly_type _ _)).
move Hb2: (fresh_inb _ _) => b2.
have ->: b1 = b2.
{
apply /is_trueP.
rewrite /b1 -Hb2 -?(rwP fresh_inP) /= allfv_poly_type_ren_poly_type.
apply: ext_allfv_poly_type.
by case.
}
case: b2 Hb2; last by rewrite /= IH.
rewrite IH ?poly_type_norm => /fresh_inP H.
apply: ext_ren_poly_type_allfv_poly_type.
rewrite allfv_poly_type_tidy.
apply: allfv_poly_type_impl H.
Admitted.

Lemma tidy_subst_poly_type {σ t} : tidy (subst_poly_type σ t) = subst_poly_type (σ >> tidy) (tidy t).
Proof.
elim: t σ; [done | by move=> ? + ? + ? /= => -> -> |].
move=> ? IH σ /=.
set b1 := (fresh_inb _ (subst_poly_type _ _)).
move Hb2: (fresh_inb _ _) => b2.
have ->: b1 = b2.
{
apply /is_trueP.
rewrite /b1 -Hb2 -?(rwP fresh_inP) /= allfv_poly_type_subst_poly_type.
apply: ext_allfv_poly_type.
case; first done.
move=> ?.
rewrite /= allfv_poly_type_ren_poly_type /=.
constructor; first done.
move=> _.
by apply: allfv_poly_type_TrueI.
}
case: b2 Hb2.
-
rewrite IH ?poly_type_norm => /fresh_inP H.
apply: ext_subst_poly_type_allfv_poly_type.
rewrite allfv_poly_type_tidy.
apply: allfv_poly_type_impl H.
case; first done.
move=> ? _ /=.
by rewrite tidy_ren_poly_type ?poly_type_norm ren_poly_type_id.
-
move=> _ /=.
rewrite IH /=.
congr poly_abs.
apply: ext_poly_type.
case; first done.
move=> ?.
Admitted.

Lemma contains_tidyI {t t'} : contains t t' -> contains (tidy t) (tidy t').
Proof.
move=> /clos_rt_rt1n_iff.
elim; first by move=> ?; apply: rt_refl.
move=> > [] s'' t'' _ IH /=.
case H: (fresh_inb _ _).
-
move: IH.
rewrite tidy_subst_poly_type.
congr contains.
rewrite ren_as_subst_poly_type.
apply: ext_subst_poly_type_allfv_poly_type.
rewrite allfv_poly_type_tidy.
move: H => /fresh_inP.
apply: allfv_poly_type_impl.
by case.
-
apply: rt_trans; last by eassumption.
apply: rt_step.
rewrite tidy_subst_poly_type.
have := contains_step_subst (s := tidy s'') (t := tidy t'').
congr contains_step.
apply: ext_poly_type.
Admitted.

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

Lemma is_simple_ren_poly_type {ξ t} : is_simple (ren_poly_type ξ t) <-> is_simple t.
Proof.
Admitted.

Lemma pure_typing_tidyRL {s n} : is_simple s -> allfv_poly_type (gt n) s -> pure_typing [many_poly_abs n s] (pure_var 0) (tidy (many_poly_abs n s)).
Proof.
rewrite (svalP tidy_many_poly_abs).
move: (sval _) => [n' ξ'] /= Hs Hns.
apply: (pure_typing_pure_var n'); first done.
rewrite tidy_is_simple; first by rewrite is_simple_ren_poly_type.
rewrite ren_poly_type_many_poly_abs.
have -> : ren_poly_type (Nat.iter n up_ren (Nat.add n')) s = s.
{
rewrite -[RHS]ren_poly_type_id.
apply: ext_ren_poly_type_allfv_poly_type.
apply: allfv_poly_type_impl Hns.
move=> ? ?.
rewrite iter_up_ren_lt; by [|lia].
}
rewrite ren_as_subst_poly_type.
Admitted.

Lemma pure_typing_tidyLR {s n} : is_simple s -> allfv_poly_type (gt n) s -> pure_typing [tidy (many_poly_abs n s)] (pure_var 0) (many_poly_abs n s).
Proof.
move=> Hs Hns.
apply: (pure_typing_pure_var n); first by reflexivity.
rewrite -tidy_ren_poly_type ren_poly_type_many_poly_abs.
have -> : ren_poly_type (Nat.iter n up_ren (Nat.add n)) s = s.
{
rewrite -[RHS]ren_poly_type_id.
apply: ext_ren_poly_type_allfv_poly_type.
apply: allfv_poly_type_impl Hns.
move=> ? ?.
rewrite iter_up_ren_lt; by [|lia].
}
rewrite -[s in contains _ s](tidy_is_simple Hs).
apply: contains_tidyI.
rewrite -[s in contains _ s]subst_poly_type_poly_var.
Admitted.

Lemma pure_typableI {Gamma M t} : pure_typing Gamma M t -> pure_typable Gamma M.
Proof.
move=> ?.
Admitted.

Lemma pure_typableE {Gamma M} : pure_typable Gamma M -> match M with | pure_var x => if (nth_error Gamma x) is None then False else True | pure_app M N => exists s t, pure_typing Gamma M (poly_arr s t) /\ pure_typing Gamma N s | pure_abs M => exists s, pure_typable (s :: Gamma) M end.
Proof.
move=> [t] [].
-
move=> n {}Gamma x >.
rewrite nth_error_map.
by case: (nth_error Gamma x).
-
move=> n > /(pure_typing_ren_poly_type (fun x => x - n)) H1.
move=> /(pure_typing_ren_poly_type (fun x => x - n)) H2 _.
move: H1 H2.
rewrite ?map_map.
rewrite map_id'.
{
move=> ?.
rewrite poly_type_norm ren_poly_type_id' /=; by [|lia].
}
move=> ? ?.
do 2 eexists.
constructor; by eassumption.
-
move=> n > /(pure_typing_ren_poly_type (fun x => x - n)) /=.
rewrite ?map_map map_id'.
{
move=> ?.
rewrite poly_type_norm ren_poly_type_id' /=; by [|lia].
}
move=> /pure_typableI ?.
eexists.
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
by exists ((1+n'), ξ').
