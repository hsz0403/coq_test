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
apply: (pure_typing_pure_abs (n + n')); by eassumption.
