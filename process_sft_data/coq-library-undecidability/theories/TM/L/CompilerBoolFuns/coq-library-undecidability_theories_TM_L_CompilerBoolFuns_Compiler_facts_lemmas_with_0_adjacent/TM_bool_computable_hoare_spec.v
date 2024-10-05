From Coq Require Import Vector List.
From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import Datatypes.Lists Tactics.LTactics Util.L_facts.
From Undecidability.TM Require Import TM_facts ProgrammingTools .
Import ListNotations VectorNotations.
From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec.
Require Import Equations.Equations.
From Undecidability.TM Require Import Hoare.
Definition TM_bool_computable_hoare_in {k n Σ} s b (v: Vector.t (list bool) k): SpecV Σ (1+k+n) := ([Custom (eq niltape)] ++ Vector.map (fun bs => Custom (eq (encBoolsTM s b bs))) v) ++ Vector.const (Custom (eq niltape)) _.
Definition TM_bool_computable_hoare_out {k n Σ} s b (bs :list bool): SpecV Σ (1+k+n) := ([Custom (eq (encBoolsTM s b bs)) ] ++ Vector.const (Custom (fun _ => True)) _)++ Vector.const (Custom (fun _ => True)) _.
Definition TM_bool_computable_hoare {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := exists n : nat, exists Σ : finType, exists s b , s <> b /\ exists M : pTM (Σ^+) unit (1 + k + n), forall v, Triple ≃≃([],TM_bool_computable_hoare_in s b v) M (fun y t => exists res, t ≃≃ ([R v res]%list,TM_bool_computable_hoare_out s b res)) /\ forall res, R v res -> exists k__steps, TripleT ≃≃([],TM_bool_computable_hoare_in s b v) k__steps M (fun y => ≃≃([]%list,TM_bool_computable_hoare_out s b res)).
Definition TM_bool_computable_hoare_in' {k n Σ} s b (v: Vector.t (list bool) k): SpecV Σ (1+n+k) := Custom (eq niltape) :: Vector.const (Custom (eq niltape)) _ ++ Vector.map (fun bs => Custom (eq (encBoolsTM s b bs))) v.
Definition TM_bool_computable_hoare_out' {n Σ} s b (bs :list bool): SpecV Σ (1+n) := Custom (eq (encBoolsTM s b bs)) :: Vector.const (Custom (fun _ => True)) _.
Definition TM_bool_computable_hoare' {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := exists n : nat, exists Σ : finType, exists s b , s <> b /\ exists M : pTM (Σ^+) unit (1 + n + k), forall v, Triple ≃≃([],TM_bool_computable_hoare_in' s b v) M (fun y t => exists res, t ≃≃ ([R v res]%list,TM_bool_computable_hoare_out' s b res)) /\ forall res, R v res -> exists k__steps, TripleT ≃≃([],TM_bool_computable_hoare_in' s b v) k__steps M (fun y => ≃≃([]%list,TM_bool_computable_hoare_out' s b res)).
Local Definition tapeOrderSwap n k:= (Fin0 ::: tabulate (n := n) (fun x => Fin.R (1 + k) x) ++ (tabulate (n := k) (fun x => Fin.L n (Fin.R 1 x)))).
Local Lemma tapeOrderSwap_dupfree k n : VectorDupfree.dupfree (tapeOrderSwap n k).
Proof.
unfold tapeOrderSwap.
econstructor.
intros [ [i Hi % (f_equal (fun x => proj1_sig (Fin.to_nat x)))] % in_tabulate | [i Hi % (f_equal (fun x => proj1_sig (Fin.to_nat x)))] % in_tabulate ] % Vector_in_app.
3: eapply Vector_dupfree_app; repeat split.
+
rewrite !Fin.R_sanity in Hi.
cbn in Hi.
lia.
+
rewrite !Fin.L_sanity, !Fin.R_sanity in Hi.
destruct (Fin.to_nat i); cbn in *; lia.
+
eapply dupfree_tabulate_injective.
eapply Fin_R_fillive.
+
eapply dupfree_tabulate_injective.
intros.
eapply Fin_R_fillive.
eapply Fin_L_fillive.
eassumption.
+
intros ? (? & ?) % in_tabulate (? & ?) % in_tabulate.
subst.
eapply (f_equal (fun H => proj1_sig (Fin.to_nat H))) in H0.
rewrite Fin.R_sanity, !Fin.L_sanity in H0.
destruct Fin.to_nat, Fin.to_nat.
cbn in *.
lia.
Local Set Keyed Unification.

Lemma TM_bool_computable_hoare_spec k R : functional R -> @TM_bool_computable_hoare k R -> @TM_bool_computable k R.
Proof.
intros Hfun (n & Σ & s & b & Hdiff & [M lab] & H).
eexists n, _, s, b.
split.
exact Hdiff.
exists M.
intros v.
specialize (H v) as [H1 H2].
split.
-
intros m.
split.
+
intros HR.
specialize H2 as [k__steps H2%TripleT_TerminatesIn].
eassumption.
cbn in H2.
destruct (H2 (([niltape] ++ Vector.map (encBoolsTM s b) v) ++ Vector.const niltape n) k__steps) as [[q' t'] Hconf].
*
split.
2:easy.
now apply TM_bool_computable_hoare_in_spec.
*
exists q', t'.
split.
eapply TM_eval_iff.
eexists.
eapply Hconf.
eapply H1 in Hconf as (m' & Hm1 & Hm2%TM_bool_computable_hoare_out_spec).
now apply TM_bool_computable_hoare_in_spec.
pose proof (Hfun _ _ _ HR Hm1) as ->.
easy.
+
intros (q' & t' & [steps Hter] % TM_eval_iff & Hout).
eapply H1 in Hter as (m' & Hm1 & Hm2%TM_bool_computable_hoare_out_spec).
now apply TM_bool_computable_hoare_in_spec.
cbn -[to_list] in *.
enough (m = m') by now subst.
eapply encBoolsTM_inj; eauto.
congruence.
-
intros q t [steps Hter] % TM_eval_iff.
eapply H1 in Hter as (m & Hm1 & Hm2%TM_bool_computable_hoare_out_spec).
now apply TM_bool_computable_hoare_in_spec.
eauto.
