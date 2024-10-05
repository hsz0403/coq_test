Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Local Open Scope logic_base.
Local Open Scope syntax.
Class Adjointness (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (prodp funcp: expr -> expr -> expr): Prop := { adjoint: forall x y z, |-- prodp x y --> z <-> |-- x --> (funcp y z) }.
Class Commutativity (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (prodp: expr -> expr -> expr): Prop := { prodp_comm_impp: forall x y, |-- prodp x y --> prodp y x }.
Class Monotonicity (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (prodp: expr -> expr -> expr): Prop := { prodp_mono: forall x1 y1 x2 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- prodp x1 y1 --> prodp x2 y2 }.
Class Associativity (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (prodp: expr -> expr -> expr): Prop := { prodp_assoc1: forall x y z, |-- prodp x (prodp y z) --> prodp (prodp x y) z; prodp_assoc2: forall x y z, |-- prodp (prodp x y) z --> prodp x (prodp y z) }.
Class LeftUnit (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (e: expr) (prodp: expr -> expr -> expr): Prop := { left_unit1: forall x, |-- prodp e x --> x; left_unit2: forall x, |-- x --> prodp e x }.
Class RightUnit (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (e: expr) (prodp: expr -> expr -> expr): Prop := { right_unit1: forall x, |-- prodp x e --> x; right_unit2: forall x, |-- x --> prodp x e }.
Class LeftDistr (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (prodp sump: expr -> expr -> expr): Prop := { left_distr1: forall x y z, |-- prodp x (sump y z) --> sump (prodp x y) (prodp x z); left_distr2: forall x y z, |-- sump (prodp x y) (prodp x z) --> prodp x (sump y z); }.
Class RightDistr (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) (prodp sump: expr -> expr -> expr): Prop := { right_distr1: forall x y z, |-- prodp (sump y z) x --> sump (prodp y x) (prodp z x); right_distr2: forall x y z, |-- sump (prodp y x) (prodp z x) --> prodp (sump y z) x; }.
Section AdjointTheorems.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {prodp funcp: expr -> expr -> expr} {Adj: Adjointness L Gamma prodp funcp}.
Section AdjointCommutativeTheorems.
Context {Comm: Commutativity L Gamma prodp}.
End AdjointCommutativeTheorems.
Section AdjointMonoTheorems.
Context {Mono: Monotonicity L Gamma prodp}.
End AdjointMonoTheorems.
End AdjointTheorems.
Section MonoTheorems.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {prodp: expr -> expr -> expr} {Mono: Monotonicity L Gamma prodp}.
End MonoTheorems.
Section AssocTheorems.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {prodp: expr -> expr -> expr} {e: expr} {Mono: Monotonicity L Gamma prodp} {Assoc: Associativity L Gamma prodp} {LU: LeftUnit L Gamma e prodp} {RU: RightUnit L Gamma e prodp}.
End AssocTheorems.
Section DistrCommTheorems.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {prodp sump: expr -> expr -> expr} {Comm: Commutativity L Gamma prodp} {Mono: Monotonicity L Gamma sump}.
End DistrCommTheorems.
Section CommForSimpleAssocConstruction.
Context {L: Language} {minL: MinimumLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {prodp: expr -> expr -> expr} {Comm: Commutativity L Gamma prodp} {Mono: Monotonicity L Gamma prodp}.
End CommForSimpleAssocConstruction.

Lemma assoc_fold_right_fold_left: forall xs, |-- fold_right prodp e xs --> fold_left prodp xs e.
Proof.
intros.
induction xs.
+
simpl.
apply provable_impp_refl.
+
simpl.
apply assoc_fold_right_cons.
