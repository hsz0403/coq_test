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
by apply: contains_many_poly_abs_closedI.
