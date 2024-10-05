Require Import List Lia Relation_Definitions Relation_Operators Operators_Properties.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts iipc2_facts pure_typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition K' M N := pure_app (pure_abs (ren_pure_term S M)) N.
Fixpoint leftmost_poly_var (t: poly_type) := match t with | poly_var x => Some x | poly_arr s t => leftmost_poly_var s | poly_abs t => if leftmost_poly_var t is Some (S x) then Some x else None end.
Fixpoint leftmost_path_length (t: poly_type) := match t with | poly_var x => 0 | poly_arr s t => 1 + leftmost_path_length s | poly_abs t => leftmost_path_length t end.
Definition Mω := pure_abs (pure_app (pure_var 0) (pure_var 0)).
Definition M_Wells N := pure_abs (K' (pure_var 0) (K' (pure_abs (pure_app (pure_var 1) (pure_app (pure_var 1) (pure_var 0)))) N)).
Definition M_Wells_J N := pure_app (pure_abs (K' (pure_app (pure_var 0) (pure_var 0)) (pure_app (pure_var 0) Mω))) (M_Wells N).
Ltac first_pure_typingE := match goal with | |- pure_typing _ (pure_app _ _) (poly_var _) -> _ => move=> /pure_typingE' [?] [?] [+] [+] ? | |- pure_typing _ (pure_app _ _) (poly_arr _ _) -> _ => move=> /pure_typingE' [?] [?] [+] [+] ? | |- pure_typing _ (pure_app _ _) _ -> _ => move=> /pure_typingE [?] [?] [?] [?] [+] [+] [? ?] | |- pure_typing _ (pure_abs _) (poly_arr _ _) -> _ => move=> /pure_typingE' | |- pure_typing _ (pure_abs _) _ -> _ => move=> /pure_typingE [?] [?] [?] [+ ?] | |- pure_typing _ (pure_var _) (poly_var _) -> _ => move=> /pure_typingE' [?] [[?]] ? | |- pure_typing _ (pure_var _) (poly_arr _ _) -> _ => move=> /pure_typingE' [?] [[?]] ? | |- pure_typing _ (pure_var _) _ -> _ => move=> /pure_typingE [?] [?] [?] [[?]] [? ?] | |- pure_typing _ (K' _ _) _ -> _ => move=> /pure_typing_K'E [] | |- pure_typable _ (K' _ _) -> _ => move=> /pure_typable_K'E [] | |- pure_typable _ (pure_var _) -> _ => move=> _ | |- pure_typable _ (pure_app _ _) -> _ => move=> /pure_typableE [?] [?] [] | |- pure_typable _ (pure_abs _) -> _ => move=> /pure_typableE [?] end.
Ltac simplify_poly_type_eqs := match goal with | H : contains (poly_var _) _ |- _ => move: H => /containsE ? | H : contains (poly_arr _ _) _ |- _ => move: H => /containsE ? | H : contains (many_poly_abs _ (poly_arr _ _)) (poly_arr _ _) |- _ => move: H => /contains_poly_arrE [?] [?] [? ?] | H : contains (subst_poly_type (fold_right scons poly_var _) _) _ |- _ => move /contains_subst_poly_type_fold_rightE in H; rewrite ?many_poly_abs_many_poly_abs in H | H : many_poly_abs _ (poly_var _) = subst_poly_type _ _ |- _ => move: H => /many_poly_abs_poly_var_eq_subst_poly_typeE => [[?]] [?] [?] [? ?] | H : contains (ren_poly_type _ (ren_poly_type _ _)) _ |- _ => rewrite ?renRen_poly_type /= in H | H : contains (ren_poly_type _ (many_poly_abs ?n (poly_var (?n + _)))) _ |- _ => rewrite ren_poly_type_many_poly_abs /= iter_up_ren in H | H : contains (ren_poly_type _ (many_poly_abs ?n (poly_arr (poly_var (?n + _)) (poly_var (?n + _))))) _ |- _ => rewrite ren_poly_type_many_poly_abs /= ?iter_up_ren in H | H : contains (many_poly_abs ?n (poly_var (?n + _))) _ |- _ => move: H => /contains_many_poly_abs_free [?] [?] [? ?] | H : poly_arr _ _ = many_poly_abs ?n _ |- _ => (have ? : n = 0 by move : (n) H; case); subst n; rewrite /= in H | H : many_poly_abs ?n _ = poly_var _ |- _ => (have ? : n = 0 by move : (n) H; case); subst n; rewrite /= in H | H : poly_var _ = poly_var _ |- _ => move: H => [?] end.
Arguments funcomp {X Y Z} _ _ / _.
Definition poly_abba := poly_abs (poly_abs (poly_arr (poly_var 1) (poly_arr (poly_var 0) (poly_arr (poly_var 0) (poly_var 1))))).
Fixpoint trace_poly_type (e: nat) (t: poly_type) : pure_term := match t with | poly_var x => pure_var x | poly_arr s t => pure_app (pure_app (pure_var e) (trace_poly_type e t)) (trace_poly_type e s) | poly_abs _ => pure_var 0 end.
Module pure_typable_intro_prenex_aux.
End pure_typable_intro_prenex_aux.
Import pure_typable_intro_prenex_aux.

Theorem pure_typable_intro_prenex M s n : is_simple s -> allfv_poly_type (gt n) s -> { N | forall Gamma, pure_typable (map tidy (many_poly_abs n s :: Gamma)) M <-> pure_typable (map tidy Gamma) N }.
Proof.
move=> Hs Hns.
pose N0 := many_pure_term_abs n (trace_poly_type n s).
pose N1 := pure_abs (K' (many_pure_app (pure_var 0) (repeat (pure_var 2) n)) (many_pure_app (pure_var 0) (repeat (pure_var 3) n))).
pose N2 := pure_app (ren_pure_term (Nat.add 4) (pure_abs M)) (pure_app N1 N0).
have [N2_1 HN2_1]:= pure_typing_intro_poly_abba N2.
have [N2_2 HN2_2] := pure_typable_intro_poly_bot N2_1.
have [N2_3 HN2_3] := pure_typable_intro_poly_var_0 N2_2.
exists N2_3 => Gamma.
constructor.
-
move=> [tM] HtM.
apply /HN2_3 /HN2_2 /HN2_1 => {HN2_3 HN2_2 HN2_1}.
eexists.
apply: (pure_typing_pure_app_simpleI (s := tidy (many_poly_abs n s))).
+
move=> /=.
apply: pure_typing_pure_abs_simpleI.
move: HtM => /(pure_typing_ren_poly_type S) HtM.
apply: pure_typing_ren_pure_term; first by eassumption.
case.
*
move=> ? /= <-.
rewrite -tidy_ren_poly_type.
congr Some.
congr tidy.
rewrite ren_poly_type_allfv_id ?allfv_poly_type_many_poly_abs; last done.
apply: allfv_poly_type_impl Hns => ? ?.
rewrite iter_scons_lt; by [lia |].
*
move=> ? ? /= <-.
congr nth_error.
rewrite ?map_map.
apply: map_ext => ?.
by rewrite tidy_ren_poly_type.
+
apply: (pure_typing_pure_app_simpleI (s := tidy (Nat.iter n (fun s' => poly_abs (poly_arr (poly_var 0) s')) s))).
*
rewrite -/(tidy (poly_arr _ _)).
apply: pure_typing_tidyI.
apply: pure_typing_pure_abs_simpleI.
apply: pure_typing_K'I.
**
apply: aux_pure_typing_gxs; [done | by apply: pure_typing_pure_var_simpleI].
**
apply: aux_pure_typable_gys; [done | by apply: pure_typing_pure_var_simpleI].
*
apply: pure_typing_tidyI.
rewrite /N0.
have ->: trace_poly_type n = trace_poly_type (n+0) by congr trace_poly_type; lia.
apply: aux_pure_typing_N0; [done | by apply: allfv_poly_type_impl Hns; lia | | done].
rewrite allfv_poly_type_many_poly_abs.
apply: allfv_poly_type_impl Hns.
move=> ? ?.
rewrite iter_scons_lt; by [lia|].
-
move /HN2_3 /HN2_2 /HN2_1 => {HN2_3 HN2_2 HN2_1}.
rewrite /N2 /N1 /N0 /= => {N2_3 N2_2 N2_1}.
move=> /pure_typableE [?] [?] [].
move=> /pure_typingE' HM.
move=> /pure_typingE [n3] [?] [?] [?] [+] [+] [H2C ?].
subst.
move=> /pure_typingE'.
move=> /pure_typing_K'E [HN1_1] HN1_2.
move=> /pure_typing_many_pure_term_absE [nss] [?] [?] [?].
subst.
move: HN1_2 => /pure_typable_many_pure_app_repeat_poly_var.
evar (r : poly_type) => /(_ (n3 + 0) r).
apply: unnest; first by subst r.
apply: unnest; first done.
move=> Hnss.
set Gamma' := (Gamma' in pure_typing Gamma' _ _).
have : exists ss Gamma'', length ss = length nss /\ Gamma' = ss ++ poly_abba :: Gamma'' /\ Forall (fun 's => exists n x, s = many_poly_abs n (poly_var (n + x))) ss.
{
rewrite /Gamma'.
elim /rev_ind: (nss) Hnss; first by move=> ?; exists []; eexists.
clear=> [[n s]] nss IH /Forall_appP [/IH] {}IH /Forall_singletonP [n0] [x0] ->.
rewrite fold_left_app app_length.
move: IH => [ss] [Gamma''] [<-] /= [->] Hss.
eexists (_ :: map (ren_poly_type (Nat.add n)) ss), (map (ren_poly_type (Nat.add n)) Gamma'').
rewrite /= map_length map_app /= Forall_consP Forall_mapP.
constructor; first by lia.
constructor; first done.
constructor; first by do 2 eexists.
apply: Forall_impl Hss => ? [?] [? ->].
rewrite ren_poly_type_many_poly_abs /= iter_up_ren.
by do 2 eexists.
}
move=> [ss] [?] [H1ss] [-> {Gamma'}] H2ss.
rewrite -H1ss.
move=> /pure_typing_tidyI.
rewrite map_app /=.
have [ns [H1ns H2ns]] : exists ns, length ss = length ns /\ map tidy ss = map poly_var ns.
{
elim: (ss) H2ss; first by move=> _; exists [].
clear=> s ss IH /Forall_consP [] [?] [n] -> /IH [ns] /= [-> ->].
exists (n :: ns).
constructor; first done.
rewrite tidy_many_poly_abs_le /=; first by lia.
congr cons.
congr poly_var.
by lia.
}
rewrite H1ns H2ns.
move=> /(pure_typing_trace_poly_typeE (n := 0)).
rewrite -H1ns H1ss tidy_tidy => /(_ ltac:(done) ltac:(done)).
move: HN1_1 => /pure_typing_fold_right_many_pure_app /= => /(_ _ ltac:(done)).
move=> [n6] [ξs] [n7] [?] [? H3C].
subst.
move=> H2s.
move: HM => /=.
set s0 := (s0 in pure_typing (s0 :: _) _ _).
set Gamma0 := (Gamma0 in pure_typing (s0 :: _ :: _ :: _ :: _ :: Gamma0) _ _).
move=> /(pure_typing_ren_pure_term_allfv_pure_term (scons 0 (scons 0 (scons 0 (scons 0 (scons 0 S))))) (Delta := s0 :: Gamma0)).
apply: unnest.
{
rewrite allfv_pure_term_ren_pure_term /=.
apply: allfv_pure_term_TrueI.
by case.
}
rewrite renRen_pure_term /= ren_pure_term_id'; first by case.
subst Gamma0.
have H4s : allfv_poly_type (fun=> False) (tidy (many_poly_abs (length nss) s)).
{
rewrite allfv_poly_type_tidy allfv_poly_type_many_poly_abs.
apply: allfv_poly_type_impl Hns => ? ?.
rewrite iter_scons_lt; by [|lia].
}
have : pure_typing [tidy (many_poly_abs (length nss) s)] (pure_var 0) (tidy s0).
{
have H3s : [tidy (many_poly_abs (length nss) s)] = map tidy [tidy (many_poly_abs (length nss) s)] by rewrite /= tidy_tidy.
rewrite /s0 {s0}.
rewrite H3s.
apply: pure_typing_tidy_many_poly_abs_closed; first done.
rewrite H3s.
apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
rewrite H3s.
apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
rewrite tidy_ren_poly_type -H2s ?poly_type_norm /=.
rewrite -[s in ren_poly_type _ s](tidy_is_simple Hs) -tidy_ren_poly_type -/(map tidy [_]).
apply: pure_typing_tidyI.
apply: (pure_typing_pure_var 0); first done.
rewrite ren_poly_type_id ren_as_subst_poly_type.
by apply: contains_many_poly_abs_closedI.
}
move=> /pure_typing_weaken_closed => /(_ []) H /pure_typing_tidyI /= /H{H} => /(_ ltac:(done)).
move=> /(pure_typing_ren_poly_type (fun x => x - 1)) /= /pure_typableI.
congr pure_typable.
congr cons.
+
rewrite ren_poly_type_allfv_id; last done.
by apply: allfv_poly_type_impl H4s.
+
rewrite ?map_map.
apply: map_ext => ?.
rewrite ?tidy_ren_poly_type tidy_tidy ?poly_type_norm /=.
apply: ren_poly_type_id'.
by lia.
