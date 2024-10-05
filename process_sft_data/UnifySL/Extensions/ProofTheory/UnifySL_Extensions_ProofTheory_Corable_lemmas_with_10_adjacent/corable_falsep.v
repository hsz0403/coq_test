Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
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
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.Extensions.ProofTheory.Stable.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Class Corable (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} (Gamma: Provable L) := { corable: expr -> Prop; corable_pstable: PropositionalStable L Gamma corable; corable_sstable: SeparationStable L Gamma corable; corable_sabs: SeparationAbsorbStable L Gamma corable }.
Section Corable.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {sepconL: SepconLanguage L} {wandL: WandLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma} {sepconAX: SepconAxiomatization L Gamma} {wandAX: WandAxiomatization L Gamma} {CosAX: Corable L Gamma}.
Instance corable_proper_iff: Proper ((fun x y => |-- x <--> y) ==> iff) corable.
Proof.
apply (@stable_proper_iffp L _ _ Gamma corable corable_pstable); auto.
End Corable.
Existing Instance corable_proper_iff.

Lemma corable_andp: forall x y, corable x -> corable y -> corable (x && y).
Proof.
intros.
Admitted.

Lemma corable_orp: forall x y, corable x -> corable y -> corable (x || y).
Proof.
intros.
Admitted.

Lemma corable_impp: forall x y, corable x -> corable y -> corable (x --> y).
Proof.
intros.
Admitted.

Lemma corable_iffp: forall x y, corable x -> corable y -> corable (x <--> y).
Proof.
intros.
Admitted.

Lemma corable_truep: corable TT.
Proof.
Admitted.

Lemma corable_sepcon: forall x y, corable x -> corable y -> corable (x * y).
Proof.
intros.
Admitted.

Lemma corable_wand: forall x y, corable x -> corable y -> corable (x -* y).
Proof.
intros.
Admitted.

Instance corable_proper_iff: Proper ((fun x y => |-- x <--> y) ==> iff) corable.
Proof.
Admitted.

Lemma corable_andp_sepcon1: forall x y z, corable x -> |-- (x && y) * z <--> x && (y * z).
Proof.
intros.
Admitted.

Lemma corable_andp_sepcon2: forall x y z, corable y -> |-- (x && y) * z <--> y && (x * z).
Proof.
intros.
rewrite andp_comm.
Admitted.

Lemma corable_sepcon_andp1: forall x y z, corable y -> |-- x * (y && z) <--> y && (x * z).
Proof.
intros.
rewrite sepcon_comm.
rewrite (sepcon_comm x z).
Admitted.

Lemma corable_sepcon_andp2: forall x y z, corable z -> |-- x * (y && z) <--> z && (x * y).
Proof.
intros.
rewrite andp_comm.
Admitted.

Lemma corable_sepcon_imply_andp: forall x y, corable x -> corable y -> |-- x * y --> x && y.
Proof.
intros.
rewrite <- (andp_truep y) at 1.
rewrite corable_sepcon_andp1 by auto.
rewrite <- (andp_truep x) at 1.
rewrite corable_andp_sepcon1 by auto.
rewrite <- andp_assoc.
rewrite (andp_comm x y).
Admitted.

Lemma corable_sepcon_is_andp {ExtsGamma: ExtSeparationLogic L Gamma}: forall x y, corable x -> corable y -> |-- x * y <--> x && y.
Proof.
intros.
rewrite <- (andp_truep y) at 1.
rewrite corable_sepcon_andp1 by auto.
rewrite <- (andp_truep x) at 1.
rewrite corable_andp_sepcon1 by auto.
rewrite <- andp_assoc.
rewrite (andp_comm x y).
rewrite provable_truep_sepcon_truep.
rewrite andp_truep.
Admitted.

Lemma corable_falsep: corable FF.
Proof.
apply (@falsep_stable L _ _ Gamma corable corable_pstable); auto.
