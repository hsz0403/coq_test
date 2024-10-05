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
by rewrite map_app /= ren_poly_type_closed_id.
