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

Lemma typing_contains {s t Gamma P} : contains s t -> typing Gamma P s -> exists Q, erase P = erase Q /\ typing Gamma Q t.
Proof.
move=> /clos_rt_rt1n_iff => H.
elim: H P.
-
move=> ? ? ?.
by eexists.
-
move=> ? ? ? [] s' ? _ IH P.
Admitted.

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

Lemma pure_typing_ren_poly_type {Gamma M t} ξ : pure_typing Gamma M t -> pure_typing (map (ren_poly_type ξ) Gamma) M (ren_poly_type ξ t).
Proof.
move=> /pure_typing_to_typing [?] [->] /(typing_ren_poly_type ξ) /typing_to_pure_typing.
congr pure_typing.
by apply: erase_ren_term_id.
