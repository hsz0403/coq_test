Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Class SeparationLogic_Precise (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} (Gamma: Provable L) := { precise: expr -> Prop; precise_sepcon: forall x y, precise x -> precise y -> precise (x * y) }.
Class SeparationLogic_PureFact (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} (Gamma: Provable L) := { pure_fact: expr -> Prop; pure_falsep: pure_fact FF; pure_andp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x && y); pure_orp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x || y); pure_impp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x --> y); pure_specon: forall x y, pure_fact x -> pure_fact y -> pure_fact (x * y); pure_wand: forall x y, pure_fact x -> pure_fact y -> pure_fact (x -* y); andp_sepcon: forall x y z, pure_fact x -> |-- (x && (y * z)) <--> ((x && y) * z) }.