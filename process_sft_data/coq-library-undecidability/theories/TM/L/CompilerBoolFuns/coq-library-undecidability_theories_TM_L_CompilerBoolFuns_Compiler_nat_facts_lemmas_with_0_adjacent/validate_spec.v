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

Lemma validate_spec {k} (v : Vector.t (list bool) k) : validate (Vector.to_list v) = true <-> exists v', v = Vector.map (List.repeat true) v'.
Proof.
induction v; cbn; try fold (Vector.to_list v) in *; try fold (validate (Vector.to_list v)) in *.
-
split; try congruence.
intros _.
now exists [].
-
split.
+
intros [H1 [v' ->] % IHv] % andb_true_iff.
eapply validate_spec_help in H1 as [m ->].
now exists (m :: v').
+
intros (v' & H).
dependent elimination v'.
cbn in H.
eapply Vector.cons_inj in H as [-> ->].
eapply andb_true_iff.
split.
*
clear.
rename h0 into n.
induction n; cbn; congruence.
*
eapply IHv.
eauto.
