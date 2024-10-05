Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.TraceSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.
Require Import Logic.HoareLogic.GuardedHoareTriple_TraceSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.
Section soundness.
Existing Instance unit_kMD.
Context {P: ProgrammingLanguage} {MD: Model} {J: Join model} {SA: SeparationAlgebra model} {R: Relation model} {po_R: PreOrder Krelation} {DCSA: DownwardsClosedSeparationAlgebra model} {UCSA: UpwardsClosedSeparationAlgebra model} {Res: Resource} {Ac: Action} {Acr: Action_resource Ac Res} {nAcr: NormalAction_resource Ac Res} {TS: TraceSemantics P (resources * model) Ac} {AIr: ActionInterpret_resource model Ac Res ac_sem} {SAAIr: @SAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (fun a => ~ is_resources_action a)} {KAIr: @KActionInterpret_resource (resources * model) Ac ac_sem (RelProd (discPred_R resource) R)}.
Instance KSAAIr: @KSAActionInterpret_resource (resources * model) Ac ac_sem (@prod_Join _ _ (Pred_Join resource) J) (RelProd (discPred_R resource) R) (fun a => ~ is_resources_action a) := ordered_and_frame_AIr _ _ _.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsepconSM: FlatSemantics.SepconSemantics L MD tt SM}.
Class LegalInvariants (Inv: resource * (model -> Prop) -> Prop): Prop := { at_most_one_invariant: forall r I1 I2, Inv (r, I1) -> Inv (r, I2) -> I1 = I2; invariant_mono: forall r I, Inv (r, I) -> forall s1 s2, I s1 -> s1 <= s2 -> I s2; invariant_precise: forall r I, Inv (r, I) -> forall s, (exists s', (fun s' => exists f, I f /\ join s' f s) s') -> (exists s', greatest (fun s' => exists f, I f /\ join s' f s) s') }.
End soundness.

Lemma SRA_triple_spec {c2tSRA: StructuralResourceAccess P Ac Res c2t}: forall (Inv: (resource * (model -> Prop)) -> Prop) (Pre: expr) (c: cmd) (Post: expr), guarded_triple_partial_valid Inv Pre c Post <-> (forall s_pre A_post ms_post, KRIPKE: s_pre |= Pre -> @traces_access _ _ (ThreadLocal_ActionInterpret_resource _ Inv) (cmd_denote c) (fun _ => False, s_pre) (lift_function (pair A_post) ms_post) -> match ms_post with | Error => False | NonTerminating => True | Terminating s_post => KRIPKE: s_post |= Post end).
Proof.
intros.
split.
+
intros.
hnf in H.
inversion H1; subst.
replace (lift_function (pair A_post) ms_post) with (lift_function (pair (fun _:resource => False)) ms_post) in H3.
2: {
destruct ms_post as [| | ms_post]; auto.
simpl lift_function in H3.
eapply start_by_Aacq_trace_acc_spec in H3; [subst; auto |].
intros; eapply resource_sequential; eauto.
}
apply (H s_pre ms_post); auto.
apply (traces_access_intro tr); auto.
+
intros.
hnf; intros.
apply (H s_pre (fun _ => False) ms_post); auto.
