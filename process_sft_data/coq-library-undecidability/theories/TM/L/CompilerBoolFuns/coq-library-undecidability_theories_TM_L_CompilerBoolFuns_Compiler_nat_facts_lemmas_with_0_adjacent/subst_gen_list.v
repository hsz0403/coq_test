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

Lemma subst_gen_list {k} {X} {Hr : registered X} u n : n >= k -> subst (gen_list (X := X) (many_vars k)) n u = gen_list (X := X) (many_vars k).
Proof.
induction k in n |- *; rewrite ?many_vars_S; cbn.
-
rewrite subst_closed.
2:Lproc.
reflexivity.
-
intros Hn.
rewrite subst_closed.
2: Lproc.
destruct (Nat.eqb_spec k n); try lia.
rewrite IHk.
reflexivity.
lia.
