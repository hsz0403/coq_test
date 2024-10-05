Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Module IntuitionisticPropositionalLogic.
Section IntuitionisticPropositionalLogic.
Context {Sigma: PropositionalLanguage.PropositionalVariables}.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
Inductive provable: expr -> Prop := | modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y | axiom1: forall x y, provable (x --> (y --> x)) | axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)) | andp_intros: forall x y, provable (x --> y --> x && y) | andp_elim1: forall x y, provable (x && y --> x) | andp_elim2: forall x y, provable (x && y --> y) | orp_intros1: forall x y, provable (x --> x || y) | orp_intros2: forall x y, provable (y --> x || y) | orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z)) | falsep_elim: forall x, provable (FF --> x).
Instance GP: Provable PropositionalLanguage.L := Build_Provable _ provable.
Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.
Instance AX: NormalAxiomatization PropositionalLanguage.L GP GD := Provable2Derivable_Normal.
Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
apply axiom2.
Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
apply falsep_elim.
End IntuitionisticPropositionalLogic.
End IntuitionisticPropositionalLogic.
Module DeMorganPropositionalLogic.
Section DeMorganPropositionalLogic.
Context {Sigma: PropositionalLanguage.PropositionalVariables}.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
Inductive provable: expr -> Prop := | modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y | axiom1: forall x y, provable (x --> (y --> x)) | axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)) | andp_intros: forall x y, provable (x --> y --> x && y) | andp_elim1: forall x y, provable (x && y --> x) | andp_elim2: forall x y, provable (x && y --> y) | orp_intros1: forall x y, provable (x --> x || y) | orp_intros2: forall x y, provable (y --> x || y) | orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z)) | falsep_elim: forall x, provable (FF --> x) | weak_excluded_middle: forall x, provable (~~ x || ~~ ~~ x).
Instance GP: Provable PropositionalLanguage.L := Build_Provable _ provable.
Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.
Instance AX: NormalAxiomatization PropositionalLanguage.L GP GD := Provable2Derivable_Normal.
Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
apply axiom2.
Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
apply falsep_elim.
Instance dmpAX: DeMorganPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
apply weak_excluded_middle.
End DeMorganPropositionalLogic.
End DeMorganPropositionalLogic.
Module GodelDummettPropositionalLogic.
Section GodelDummettPropositionalLogic.
Context {Sigma: PropositionalLanguage.PropositionalVariables}.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
Inductive provable: expr -> Prop := | modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y | axiom1: forall x y, provable (x --> (y --> x)) | axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)) | andp_intros: forall x y, provable (x --> y --> x && y) | andp_elim1: forall x y, provable (x && y --> x) | andp_elim2: forall x y, provable (x && y --> y) | orp_intros1: forall x y, provable (x --> x || y) | orp_intros2: forall x y, provable (y --> x || y) | orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z)) | falsep_elim: forall x, provable (FF --> x) | impp_choice: forall x y, provable ((x --> y) || (y --> x)).
Instance GP: Provable PropositionalLanguage.L := Build_Provable _ provable.
Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.
Instance AX: NormalAxiomatization PropositionalLanguage.L GP GD := Provable2Derivable_Normal.
Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
apply axiom2.
Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
apply falsep_elim.
Instance gdpAX: GodelDummettPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
apply impp_choice.
Instance dmpAX: DeMorganPropositionalLogic PropositionalLanguage.L GP.
Proof.
apply GodelDummett2DeMorgan.
End GodelDummettPropositionalLogic.
End GodelDummettPropositionalLogic.
Module ClassicalPropositionalLogic.
Section ClassicalPropositionalLogic.
Context {Sigma: PropositionalLanguage.PropositionalVariables}.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
Inductive provable: expr -> Prop := | modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y | axiom1: forall x y, provable (x --> (y --> x)) | axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)) | andp_intros: forall x y, provable (x --> y --> x && y) | andp_elim1: forall x y, provable (x && y --> x) | andp_elim2: forall x y, provable (x && y --> y) | orp_intros1: forall x y, provable (x --> x || y) | orp_intros2: forall x y, provable (y --> x || y) | orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z)) | falsep_elim: forall x, provable (FF --> x) | excluded_middle: forall x, provable (x || (x --> FF)).
Instance GP: Provable PropositionalLanguage.L := Build_Provable _ provable.
Instance GD: Derivable PropositionalLanguage.L := Provable2Derivable.
Instance AX: NormalAxiomatization PropositionalLanguage.L GP GD := Provable2Derivable_Normal.
Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
apply axiom2.
Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
apply falsep_elim.
Instance cpAX: ClassicalPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
apply excluded_middle.
Instance gdpAX: GodelDummettPropositionalLogic PropositionalLanguage.L GP.
Proof.
apply Classical2GodelDummett.
Instance dmpAX: DeMorganPropositionalLogic PropositionalLanguage.L GP.
Proof.
apply GodelDummett2DeMorgan.
End ClassicalPropositionalLogic.
End ClassicalPropositionalLogic.

Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
Admitted.

Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
Admitted.

Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
Admitted.

Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
Admitted.

Instance dmpAX: DeMorganPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
Admitted.

Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
Admitted.

Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
Admitted.

Instance gdpAX: GodelDummettPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
Admitted.

Instance dmpAX: DeMorganPropositionalLogic PropositionalLanguage.L GP.
Proof.
Admitted.

Instance minAX: MinimumAxiomatization PropositionalLanguage.L GP.
Proof.
constructor.
+
apply modus_ponens.
+
apply axiom1.
+
Admitted.

Instance ipAX: IntuitionisticPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
+
apply andp_intros.
+
apply andp_elim1.
+
apply andp_elim2.
+
apply orp_intros1.
+
apply orp_intros2.
+
apply orp_elim.
+
Admitted.

Instance gdpAX: GodelDummettPropositionalLogic PropositionalLanguage.L GP.
Proof.
Admitted.

Instance dmpAX: DeMorganPropositionalLogic PropositionalLanguage.L GP.
Proof.
Admitted.

Instance cpAX: ClassicalPropositionalLogic PropositionalLanguage.L GP.
Proof.
constructor.
apply excluded_middle.
