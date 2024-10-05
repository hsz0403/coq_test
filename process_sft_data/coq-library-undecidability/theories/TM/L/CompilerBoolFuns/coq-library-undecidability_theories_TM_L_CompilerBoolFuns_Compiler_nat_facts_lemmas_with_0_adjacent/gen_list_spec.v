Require Import Equations.Equations.
From Undecidability.Shared.Libs.PSL Require Import Vectors.
From Coq Require Import Vector List.
From Undecidability.L Require Import L LTactics L_facts Functions.Eval Functions.Decoding Functions.Encoding.
From Undecidability.L.Datatypes Require Import LBool Lists LVector List.List_fold.
From Undecidability.L.Complexity.LinDecode Require Import LTDbool LTDlist LTDnat.
From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec NaryApp ClosedLAdmissible Compiler_facts.
Import ListNotations.
Import VectorNotations.
Import L_Notations.
Fixpoint gen_list {k} {X} {Hr : registered X} (v : Vector.t nat k) : term := match v with | [] => ext (@nil X) | n :: v => ext (@Datatypes.cons X) (var n) (@gen_list _ X Hr v) end.
Definition validate (l : list (list bool)) := forallb (forallb (fun x => x)) l.
Definition idbool := (fun x : bool => x).
Definition forallb' := @forallb bool.
Definition alltrue x := idbool x.
Definition forallb'' := @forallb (list bool).
Local Instance term_forallb' : computable forallb' | 0.
Proof.
unfold forallb'.
extract.
Local Instance term_forallb'' : computable forallb'' | 0.
Proof.
unfold forallb''.
extract.
Instance term_idbool : computable idbool.
Proof.
extract.
Instance term_alltrue : computable alltrue.
Proof.
extract.
Remove Hints term_forallb : typeclass_instances.
Instance term_validate : computable validate.
Proof.
change (computable (fun l => forallb'' (forallb' alltrue) l)).
extract.

Lemma gen_list_spec {k} {X} {Hr : registered X} (v' : Vector.t X k) : many_subst (gen_list (X := X) (many_vars k)) 0 (Vector.map enc v') == enc v'.
Proof.
induction v'; cbn - [many_vars].
-
Lsimpl_old.
-
rewrite many_vars_S.
cbn.
rewrite Nat.eqb_refl.
rewrite subst_closed; [ | now Lproc ].
rewrite subst_gen_list; try lia.
rewrite many_subst_app.
rewrite many_subst_closed.
2:Lproc.
rewrite IHv'.
unfold enc at 2.
cbn.
now Lsimpl.
