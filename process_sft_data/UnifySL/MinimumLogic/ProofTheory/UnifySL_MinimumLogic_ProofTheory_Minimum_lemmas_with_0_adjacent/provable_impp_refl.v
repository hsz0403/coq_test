Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfSequentCalculus.
Local Open Scope logic_base.
Local Open Scope syntax.
Definition multi_imp {L: Language} {minL: MinimumLanguage L} (xs: list expr) (y: expr): expr := fold_right impp y xs.
Class NormalAxiomatization (L: Language) {minL: MinimumLanguage L} (GammaP: Provable L) (GammaD: Derivable L): Type := { derivable_provable: forall Phi y, derivable Phi y <-> exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y) }.
Class MinimumAxiomatization (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) := { modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y; axiom1: forall x y, |-- (x --> (y --> x)); axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z)) }.
Class MinimumSequentCalculus (L: Language) {minL: MinimumLanguage L} (Gamma: Derivable L) := { deduction_modus_ponens: forall Phi x y, Phi |-- x -> Phi |-- x --> y -> Phi |-- y; deduction_impp_intros: forall Phi x y, Phi;; x |-- y -> Phi |-- x --> y }.
Section DerivableRulesFromAxiomatization.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma}.
End DerivableRulesFromAxiomatization.
Section DerivableRules_multi_impp.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma}.
End DerivableRules_multi_impp.
Section Axiomatization2SequentCalculus.
Context {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {AX: NormalAxiomatization L GammaP GammaD}.
Context {minAX: MinimumAxiomatization L GammaP}.
End Axiomatization2SequentCalculus.
Section DerivableRulesFromSequentCalculus.
Context {L: Language} {GammaD: Derivable L} {bSC: BasicSequentCalculus L GammaD}.
Context {minL: MinimumLanguage L} {minSC: MinimumSequentCalculus L GammaD}.
End DerivableRulesFromSequentCalculus.
Section SequentCalculus2Axiomatization.
Context {L: Language} {GammaP: Provable L} {GammaD: Derivable L} {minL: MinimumLanguage L} {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD}.
End SequentCalculus2Axiomatization.
Section Transformation.
Context {L: Language} {minL: MinimumLanguage L}.
Definition Provable2Derivable {GammaP: Provable L}: Derivable L := Build_Derivable L (fun Phi y => exists xs, Forall (fun x => Phi x) xs /\ |-- multi_imp xs y).
Definition Provable2Derivable_Normal {GammaP: Provable L}: NormalAxiomatization L GammaP Provable2Derivable := Build_NormalAxiomatization L minL GammaP Provable2Derivable (fun _ _ => iff_refl _).
Definition Derivable2Provable {GammaD: Derivable L}: Provable L := Build_Provable L (fun x => (Empty_set _) |-- x).
Definition Derivable2Provable_Normal {GammaD: Derivable L}: NormalSequentCalculus L Derivable2Provable GammaD := Build_NormalSequentCalculus L Derivable2Provable GammaD (fun _ => iff_refl _).
End Transformation.

Lemma provable_impp_refl: forall (x: expr), |-- x --> x.
Proof.
intros.
pose proof axiom2 x (x --> x) x.
pose proof axiom1 x (x --> x).
pose proof axiom1 x x.
pose proof modus_ponens _ _ H H0.
pose proof modus_ponens _ _ H2 H1.
auto.
