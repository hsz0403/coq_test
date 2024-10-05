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

Lemma L_computable_to_L_bool_computable k (R : Vector.t nat k -> nat -> Prop) : L_computable R -> L_bool_computable (fun v m => exists v' m', v = Vector.map (List.repeat true) v' /\ m = List.repeat true m' /\ R v' m').
Proof.
intros (s & Hcl & Hs) % L_computable_can_closed.
setoid_rewrite <- many_app_eq_nat in Hs.
pose (sim := many_lam k (ext validate (gen_list (X := list bool) (many_vars k)) (lam (ext (@repeat bool) (ext true) 0)) (lam Omega) (many_app s (Vector.map (fun r => ext (@length bool) (var r)) (many_vars k)))) ).
exists sim.
intros v.
setoid_rewrite <- many_app_eq.
assert (HEQ : many_app sim (Vector.map enc v) == enc (validate (Vector.to_list v)) (lam (ext (repeat (A := bool)) (ext true) 0)) (lam Omega) (many_app s (Vector.map enc (Vector.map (@List.length bool) v)))).
{
unfold sim.
rewrite many_beta.
2: eapply forall_proc_help.
rewrite !many_subst_app.
rewrite gen_list_spec.
rewrite !many_subst_many_app.
repeat (rewrite many_subst_closed; [ | now Lproc]).
rewrite Vector.map_map.
unfold enc at 1.
cbn.
Lsimpl.
eapply equiv_R.
match goal with |- context [ VectorDef.map ?f ?v] => unshelve eassert (many_app s (VectorDef.map f v) == _) as -> end.
refine (many_app s (Vector.map (@enc nat _) (Vector.map (@List.length bool) v))).
*
clear.
induction v in s |- *.
--
reflexivity.
--
rewrite many_vars_S.
cbn -[many_subst].
rewrite equiv_many_app_L.
2:{
cbn.
rewrite Nat.eqb_refl.
rewrite subst_closed.
2:Lproc.
rewrite many_subst_closed.
2: Lproc.
Lsimpl.
reflexivity.
}
rewrite <- IHv.
match goal with [ |- ?l == ?r ] => enough (l = r) as H by now rewrite H end.
cbn.
f_equal.
eapply Vector.map_ext_in.
intros a Ha.
rewrite subst_closed.
2:Lproc.
rewrite !many_subst_app.
rewrite many_subst_closed.
2:Lproc.
destruct (Nat.eqb_spec a n).
++
subst.
eapply many_var_in in Ha.
lia.
++
reflexivity.
*
reflexivity.
}
split.
-
intros m.
split.
+
intros (v' & m' & -> & -> & HR).
eapply Hs in HR.
eapply eval_iff in HR.
rewrite eval_iff.
rewrite HEQ.
Lsimpl.
change (encNatL m') with (enc m') in HR.
change (encBoolsL) with (@enc (list bool) _).
rewrite validate_spec'.
rewrite !Vector.map_map.
erewrite Vector.map_ext.
2:intros; now rewrite repeat_length.
Lsimpl_old.
+
rewrite eval_iff.
rewrite HEQ.
erewrite equiv_eval_equiv.
2:{
Lsimpl.
reflexivity.
}
intros Heval.
change (encNatL) with (@enc nat _) in *.
change (encBoolsL) with (@enc (list bool) _) in *.
match type of Heval with L_facts.eval ?l _ => assert (Hc : converges l) by eauto end.
eapply app_converges in Hc as [H1 Hc].
eapply eval_converges in Hc as [o Hc % eval_iff].
pose proof (Hc' := Hc).
eapply eval_iff in Hc'.
eapply Hs in Hc as [m' ->].
destruct (validate (to_list v)) eqn:E.
*
clear HEQ.
rewrite Hc' in Heval.
erewrite equiv_eval_equiv in Heval.
2:{
clear Heval.
Lsimpl.
reflexivity.
}
eapply validate_spec in E as [v' ->].
eexists v'.
assert (m = repeat true m') as ->.
{
eapply encBoolsL_inj.
change (encBoolsL) with (@enc (list bool) _).
eapply unique_normal_forms;[Lproc..|].
now destruct Heval as [-> _].
}
exists m'.
repeat split.
eapply Hs.
rewrite !Vector.map_map in *.
erewrite Vector.map_ext in *.
2:intros; now rewrite repeat_length.
2: reflexivity.
now eapply eval_iff.
*
erewrite equiv_eval_equiv in Heval.
2:{
clear Heval.
rewrite Hc'.
eapply beta_red.
Lproc.
rewrite subst_closed.
2:Lproc.
reflexivity.
}
now eapply Omega_diverge in Heval.
-
intros o.
rewrite eval_iff.
rewrite HEQ.
erewrite equiv_eval_equiv.
2:{
Lsimpl.
reflexivity.
}
intros Heval.
change (encNatL) with (@enc nat _) in *.
change (encBoolsL) with (@enc (list bool) _) in *.
match type of Heval with L_facts.eval ?l _ => assert (Hc : converges l) by eauto end.
eapply app_converges in Hc as [H1 Hc].
eapply eval_converges in Hc as [o' Hc % eval_iff].
pose proof (Hc' := Hc).
eapply eval_iff in Hc'.
eapply Hs in Hc as [m' ->].
destruct (validate (to_list v)) eqn:E.
*
clear HEQ.
erewrite equiv_eval_equiv in Heval.
2:{
clear Heval.
Lsimpl.
reflexivity.
}
eapply validate_spec in E as [v' ->].
rewrite !Vector.map_map in *.
erewrite Vector.map_ext in *.
2:intros; now rewrite repeat_length.
exists (repeat true m').
destruct Heval as [Heval ?].
eapply unique_normal_forms;[Lproc..|].
now rewrite Heval.
*
erewrite equiv_eval_equiv in Heval.
2:{
clear Heval.
rewrite Hc'.
eapply beta_red.
Lproc.
rewrite subst_closed.
2:Lproc.
reflexivity.
}
now eapply Omega_diverge in Heval.
Unshelve.
