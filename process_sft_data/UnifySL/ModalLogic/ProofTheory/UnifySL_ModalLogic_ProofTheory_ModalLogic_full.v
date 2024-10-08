Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.Syntax.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Class SystemK (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := { axiom_K: forall x y, |-- boxp (x --> y) --> (boxp x --> boxp y); (* a.k.a. Distribution Axiom *) rule_N: forall x, |-- x -> |-- boxp x (* a.k.a. Necessitation Rule *) }.
Class SystemT (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} := { axiom_T: forall x, |-- boxp x --> x }.
Class System4 (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} {TmGamma: SystemT L Gamma}:= { axiom_4: forall x, |-- boxp x --> boxp (boxp x) }.
Class SystemD (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} := { axiom_D: forall x, |-- boxp x --> diamondp x }.
Class SystemB (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} := { axiom_B: forall x, |-- x --> boxp (diamondp x) }.
Class System5 (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} {TmGamma: SystemT L Gamma} {s4mGamma: System4 L Gamma}:= { axiom_5: forall x, |-- diamondp x --> boxp (diamondp x) }.
Class PropositionalTransparentModality (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} := { boxp_orp: forall x y, |-- boxp (x || y) <--> boxp x || boxp y }.
Class StrongPropositionalTransparentModality (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} {pmGamma: PropositionalTransparentModality L Gamma} := { boxp_impp: forall x y, |-- boxp (x --> y) <--> (boxp x --> boxp y) }.