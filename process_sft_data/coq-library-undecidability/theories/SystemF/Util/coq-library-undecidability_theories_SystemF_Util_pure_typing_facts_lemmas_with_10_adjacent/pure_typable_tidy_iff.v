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

Lemma pure_typable_tidyI {Gamma M} : pure_typable Gamma M -> pure_typable (map tidy Gamma) M.
Proof.
Admitted.

Lemma pure_typable_many_pure_term_abs_allI M {Gamma} : pure_typable Gamma M -> pure_typable [] (many_pure_term_abs (pure_var_bound M) M).
Proof.
have := pure_var_boundP M.
move: (pure_var_bound M) => n.
elim: Gamma n M.
-
elim; first done.
move=> n IH M HnM [tM].
move=> /(pure_typing_ren_pure_term id (Delta := [poly_var 0])).
apply: unnest; first by case.
rewrite ren_pure_term_id.
move=> /(pure_typing_pure_abs 0 (Gamma := [])) /pure_typableI /IH.
rewrite /many_pure_term_abs (ltac:(lia) : S n = n + 1) -iter_plus.
apply.
move=> /=.
apply: allfv_pure_term_impl HnM.
case; first done.
move=> /=.
by lia.
-
move=> s Gamma IH [|n] M.
+
move=> HM [tM].
move=> /(pure_typing_ren_pure_term_allfv_pure_term id (Delta := [])).
rewrite ren_pure_term_id.
apply: unnest; first by apply: allfv_pure_term_impl HM; lia.
by move=> /pure_typableI.
+
move=> HnM [tM].
rewrite -[Gamma]map_ren_poly_type_id.
move=> /(pure_typing_pure_abs 0) /pure_typableI /IH.
rewrite /many_pure_term_abs (ltac:(lia) : S n = n + 1) -iter_plus.
apply.
move=> /=.
apply: allfv_pure_term_impl HnM.
case; first done.
move=> /=.
Admitted.

Lemma pure_typing_iff_type_assignment {Gamma M t} : pure_typing Gamma M t <-> type_assignment Gamma M t.
Proof.
constructor.
-
by move=> /pure_typing_to_typing [?] [->] /typing_to_type_assignment.
-
Admitted.

Lemma pure_typable_tidy_iff {Gamma1 Gamma2 M} : Forall (fun t => exists n s, t = many_poly_abs n s /\ is_simple s /\ allfv_poly_type (gt n) s) Gamma2 -> pure_typable (Gamma1 ++ map tidy Gamma2) M <-> pure_typable (Gamma1 ++ Gamma2) M.
Proof.
elim: Gamma2 Gamma1; first done.
move=> ? Gamma2 IH Gamma1 /Forall_consP [] [n] [s] [->] [Hs Hns] /IH {}IH.
constructor => /=.
-
move=> [?] /pure_typing_weaken_closed => /(_ (many_poly_abs n s)).
apply: unnest.
{
rewrite allfv_poly_type_many_poly_abs.
apply: allfv_poly_type_impl Hns.
move=> *.
rewrite iter_scons_lt; by [|lia].
}
apply: unnest; first by apply: pure_typing_tidyRL.
rewrite -/([_] ++ map tidy Gamma2) -/([_] ++ Gamma2) ?app_assoc.
by move=> /pure_typableI /IH.
-
move=> [?] /pure_typing_weaken_closed => /(_ (tidy (many_poly_abs n s))).
apply: unnest.
{
rewrite allfv_poly_type_tidy allfv_poly_type_many_poly_abs.
apply: allfv_poly_type_impl Hns.
move=> *.
rewrite iter_scons_lt; by [|lia].
}
apply: unnest; first by apply: pure_typing_tidyLR.
rewrite -/([_] ++ map tidy Gamma2) -/([_] ++ Gamma2) ?app_assoc.
by move=> /pure_typableI /IH.
