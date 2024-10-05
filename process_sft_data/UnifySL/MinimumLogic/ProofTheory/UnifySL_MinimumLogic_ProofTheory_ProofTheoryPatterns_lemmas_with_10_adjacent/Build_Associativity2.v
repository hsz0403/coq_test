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

Lemma fold_right_mono2: forall x1 x2 xs, |-- x1 --> x2 -> |-- fold_right prodp x1 xs --> fold_right prodp x2 xs.
Proof.
intros.
apply fold_right_mono; auto.
induction xs.
+
constructor.
+
constructor; auto.
Admitted.

Lemma assoc_fold_left_cons: forall x xs, |-- fold_left prodp xs (prodp e x) --> prodp x (fold_right prodp e xs).
Proof.
intros.
revert x; induction xs; intros.
+
simpl.
rewrite left_unit1.
rewrite <- right_unit2.
apply provable_impp_refl.
+
simpl.
rewrite <- prodp_assoc2.
eapply aux_minimun_rule02; [| apply IHxs].
apply fold_left_mono2.
Admitted.

Lemma assoc_fold_right_cons: forall x xs, |-- prodp x (fold_right prodp e xs) --> fold_left prodp xs (prodp e x).
Proof.
intros.
revert x; induction xs; intros.
+
simpl.
rewrite <- left_unit2.
rewrite right_unit1.
apply provable_impp_refl.
+
simpl.
rewrite prodp_assoc1.
eapply aux_minimun_rule02; [apply IHxs |].
apply fold_left_mono2.
Admitted.

Lemma assoc_fold_left_fold_right: forall xs, |-- fold_left prodp xs e --> fold_right prodp e xs.
Proof.
intros.
induction xs.
+
simpl.
apply provable_impp_refl.
+
simpl.
Admitted.

Lemma assoc_fold_right_fold_left: forall xs, |-- fold_right prodp e xs --> fold_left prodp xs e.
Proof.
intros.
induction xs.
+
simpl.
apply provable_impp_refl.
+
simpl.
Admitted.

Lemma assoc_prodp_fold_left: forall xs1 xs2, |-- prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e) --> fold_left prodp (xs1 ++ xs2) e.
Proof.
intros.
eapply aux_minimun_rule02; [apply prodp_mono; apply assoc_fold_left_fold_right |].
rewrite <- assoc_fold_right_fold_left.
induction xs1.
+
simpl.
rewrite left_unit1.
apply provable_impp_refl.
+
simpl.
rewrite prodp_assoc2.
apply prodp_mono; [apply provable_impp_refl |].
Admitted.

Lemma assoc_fold_left_app: forall xs1 xs2, |-- fold_left prodp (xs1 ++ xs2) e --> prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e).
Proof.
intros.
eapply aux_minimun_rule02; [| apply prodp_mono; apply assoc_fold_right_fold_left].
rewrite assoc_fold_left_fold_right.
induction xs1.
+
simpl.
rewrite <- left_unit2.
apply provable_impp_refl.
+
simpl.
rewrite <- prodp_assoc1.
apply prodp_mono; [apply provable_impp_refl |].
Admitted.

Lemma LeftDistr2RightDistr {LDistr: LeftDistr L Gamma prodp sump}: RightDistr L Gamma prodp sump.
Proof.
constructor.
+
intros.
rewrite (prodp_comm_impp _ x).
pose proof prodp_comm_impp x y.
pose proof prodp_comm_impp x z.
pose proof prodp_mono _ _ _ _ H H0.
rewrite <- H1.
apply left_distr1.
+
intros.
rewrite <- (prodp_comm_impp x (sump y z)).
pose proof prodp_comm_impp y x.
pose proof prodp_comm_impp z x.
pose proof prodp_mono _ _ _ _ H H0.
rewrite H1.
Admitted.

Lemma RightDistr2LeftDistr {RDistr: RightDistr L Gamma prodp sump}: LeftDistr L Gamma prodp sump.
Proof.
constructor.
+
intros.
rewrite (prodp_comm_impp x (sump y z)).
pose proof prodp_comm_impp y x.
pose proof prodp_comm_impp z x.
pose proof prodp_mono _ _ _ _ H H0.
rewrite <- H1.
apply right_distr1.
+
intros.
rewrite <- (prodp_comm_impp (sump y z) x).
pose proof prodp_comm_impp x y.
pose proof prodp_comm_impp x z.
pose proof prodp_mono _ _ _ _ H H0.
rewrite H1.
Admitted.

Lemma Build_Associativity1: (forall x y z, |-- prodp x (prodp y z) --> prodp (prodp x y) z) -> Associativity L Gamma prodp.
Proof.
intros.
constructor; auto.
intros.
rewrite <- (prodp_comm_impp (prodp y z) x).
rewrite (prodp_comm_impp (prodp x y) z).
pose proof prodp_comm_impp x y.
pose proof provable_impp_refl z.
pose proof prodp_mono _ _ _ _ H1 H0.
rewrite H2.
clear H0 H1 H2.
pose proof prodp_comm_impp z y.
pose proof provable_impp_refl x.
pose proof prodp_mono _ _ _ _ H0 H1.
rewrite <- H2.
clear H0 H1 H2.
Admitted.

Lemma Build_Associativity2: (forall x y z, |-- prodp (prodp x y) z --> prodp x (prodp y z)) -> Associativity L Gamma prodp.
Proof.
intros.
constructor; auto.
intros.
rewrite <- (prodp_comm_impp z (prodp x y)).
rewrite (prodp_comm_impp x (prodp y z)).
pose proof prodp_comm_impp y z.
pose proof provable_impp_refl x.
pose proof prodp_mono _ _ _ _ H0 H1.
rewrite H2.
clear H0 H1 H2.
pose proof prodp_comm_impp y x.
pose proof provable_impp_refl z.
pose proof prodp_mono _ _ _ _ H1 H0.
rewrite <- H2.
clear H0 H1 H2.
apply H.
