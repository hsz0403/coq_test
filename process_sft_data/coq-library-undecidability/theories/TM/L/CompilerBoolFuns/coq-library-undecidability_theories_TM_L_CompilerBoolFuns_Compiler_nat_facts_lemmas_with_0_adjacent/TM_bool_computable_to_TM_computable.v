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

Lemma TM_bool_computable_to_TM_computable k (R : Vector.t nat k -> nat -> Prop) : TM_bool_computable (fun v m => exists v' m', v = Vector.map (List.repeat true) v' /\ m = List.repeat true m' /\ R v' m') -> TM_computable R.
Proof.
unfold TM_computable.
intros (n & Σ & s & b & Hsb & M & H).
exists n, Σ, s, b.
split.
exact Hsb.
exists M.
intros v.
split.
-
intros m.
split.
+
intros HR.
specialize (H (Vector.map (repeat true) v)) as [H1 H2].
specialize (H1 (repeat true m)) as [(q & t & H1) _].
*
exists v, m.
repeat split.
eassumption.
*
exists q, t.
rewrite !encBools_nat_TM.
erewrite Vector.map_ext.
2: intros; eapply encBools_nat_TM.
rewrite Vector.map_map in H1.
exact H1.
+
intros (q & t & H1).
rewrite !encBools_nat_TM in H1.
erewrite Vector.map_ext in H1.
2: intros; eapply encBools_nat_TM.
specialize (H (Vector.map (repeat true) v)) as [H2 _].
specialize (H2 (repeat true m)) as [_ (v' & m' & Hv' & Hm' & HR)].
*
exists q, t.
rewrite Vector.map_map.
eapply H1.
*
eapply (f_equal (@length bool)) in Hm'.
rewrite !repeat_length in Hm'.
subst.
clear - Hv' HR.
induction v ; dependent elimination v'.
exact HR.
inversion Hv'.
eapply (f_equal (@length bool)) in H0.
rewrite !repeat_length in H0.
subst.
eapply IHv.
2:eassumption.
eapply Eqdep_dec.inj_pair2_eq_dec in H1.
eassumption.
eapply nat_eq_dec.
-
intros q t H1.
erewrite Vector.map_ext in H1.
2: intros; eapply encBools_nat_TM.
destruct (H (Vector.map (repeat true) v)) as [H3 [m H2]].
*
rewrite Vector.map_map.
eapply H1.
*
exists (length m).
rewrite H2.
rewrite encBools_nat_TM.
specialize (H3 m) as [_ (v' & m' & ? & -> & H3)].
--
exists q, t.
split; eauto.
rewrite Vector.map_map.
exact H1.
--
now rewrite repeat_length.
