Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Section RewriteClass1.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {Gamma: Provable L} {minAX: MinimumAxiomatization L Gamma} {ipAX: IntuitionisticPropositionalLogic L Gamma}.
Instance andp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) andp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable.
rewrite <- !deduction_theorem.
apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H.
apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H0.
pose proof derivable_assum1 empty_context (x1 && y1).
pose proof deduction_andp_elim1 _ _ _ H1.
pose proof deduction_andp_elim2 _ _ _ H1.
pose proof deduction_modus_ponens _ _ _ H2 H.
pose proof deduction_modus_ponens _ _ _ H3 H0.
apply deduction_andp_intros; auto.
Instance orp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) orp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H, H0 |- *.
apply deduction_orp_elim'.
+
eapply deduction_impp_trans; [exact H |].
apply derivable_orp_intros1.
+
eapply deduction_impp_trans; [exact H0 |].
apply derivable_orp_intros2.
Instance negp_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y)) negp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
unfold negp.
apply impp_proper_impp; auto.
apply provable_impp_refl.
Instance provable_iffp_rewrite: RewriteRelation (fun x y => |-- x <--> y).
Instance provable_iffp_equiv: Equivalence (fun x y => |-- x <--> y).
Proof.
AddSequentCalculus.
constructor.
+
hnf; intros.
rewrite provable_derivable.
apply deduction_andp_intros; apply derivable_impp_refl.
+
hnf; intros.
rewrite provable_derivable in H |- *.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
apply deduction_andp_intros; auto.
+
hnf; intros.
rewrite provable_derivable in H, H0 |- *.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
apply deduction_andp_intros; eapply deduction_impp_trans; eauto.
Instance provable_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> iff) provable.
Proof.
AddSequentCalculus.
intros.
hnf; intros.
rewrite provable_derivable in H.
rewrite provable_derivable.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
split; intro; eapply deduction_modus_ponens; eauto.
Instance impp_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) impp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H.
rewrite provable_derivable in H0.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
rewrite <- provable_derivable in H1.
rewrite <- provable_derivable in H2.
rewrite <- provable_derivable in H3.
rewrite <- provable_derivable in H4.
apply deduction_andp_intros; rewrite <- provable_derivable.
+
apply impp_proper_impp; auto.
+
apply impp_proper_impp; auto.
Instance andp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) andp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H.
rewrite provable_derivable in H0.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
rewrite <- provable_derivable in H1.
rewrite <- provable_derivable in H2.
rewrite <- provable_derivable in H3.
rewrite <- provable_derivable in H4.
apply deduction_andp_intros; rewrite <- provable_derivable.
+
apply andp_proper_impp; auto.
+
apply andp_proper_impp; auto.
Instance orp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) orp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H.
rewrite provable_derivable in H0.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
rewrite <- provable_derivable in H1.
rewrite <- provable_derivable in H2.
rewrite <- provable_derivable in H3.
rewrite <- provable_derivable in H4.
apply deduction_andp_intros; rewrite <- provable_derivable.
+
apply orp_proper_impp; auto.
+
apply orp_proper_impp; auto.
Instance iffp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) iffp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
unfold iffp.
rewrite H, H0.
apply provable_iffp_refl.
Instance negp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) negp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
unfold negp.
apply impp_proper_iffp; auto.
apply provable_iffp_refl.
End RewriteClass1.
Section RewriteClass2.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {SC: NormalSequentCalculus L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD}.
Instance derivable_proper_iffp : Proper (eq ==> (fun x y => |-- x <--> y) ==> iff) derivable.
Proof.
hnf; intros Phi Phi' ?; subst Phi'.
hnf; intros x1 x2 ?.
apply (deduction_weaken0 Phi) in H.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
split; intro; eapply deduction_modus_ponens; eauto.
End RewriteClass2.
Existing Instances andp_proper_impp orp_proper_impp negp_proper_impp provable_iffp_rewrite provable_iffp_equiv provable_proper_iffp derivable_proper_iffp impp_proper_iffp andp_proper_iffp orp_proper_iffp iffp_proper_iffp negp_proper_iffp.

Instance orp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) orp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H, H0 |- *.
apply deduction_orp_elim'.
+
eapply deduction_impp_trans; [exact H |].
apply derivable_orp_intros1.
+
eapply deduction_impp_trans; [exact H0 |].
Admitted.

Instance negp_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y)) negp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
unfold negp.
apply impp_proper_impp; auto.
Admitted.


Admitted.

Instance provable_iffp_equiv: Equivalence (fun x y => |-- x <--> y).
Proof.
AddSequentCalculus.
constructor.
+
hnf; intros.
rewrite provable_derivable.
apply deduction_andp_intros; apply derivable_impp_refl.
+
hnf; intros.
rewrite provable_derivable in H |- *.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
apply deduction_andp_intros; auto.
+
hnf; intros.
rewrite provable_derivable in H, H0 |- *.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
Admitted.

Instance provable_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> iff) provable.
Proof.
AddSequentCalculus.
intros.
hnf; intros.
rewrite provable_derivable in H.
rewrite provable_derivable.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
Admitted.

Instance impp_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) impp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H.
rewrite provable_derivable in H0.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
rewrite <- provable_derivable in H1.
rewrite <- provable_derivable in H2.
rewrite <- provable_derivable in H3.
rewrite <- provable_derivable in H4.
apply deduction_andp_intros; rewrite <- provable_derivable.
+
apply impp_proper_impp; auto.
+
Admitted.

Instance andp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) andp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H.
rewrite provable_derivable in H0.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
rewrite <- provable_derivable in H1.
rewrite <- provable_derivable in H2.
rewrite <- provable_derivable in H3.
rewrite <- provable_derivable in H4.
apply deduction_andp_intros; rewrite <- provable_derivable.
+
apply andp_proper_impp; auto.
+
Admitted.

Instance orp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) orp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable in H.
rewrite provable_derivable in H0.
rewrite provable_derivable.
pose proof deduction_andp_elim1 _ _ _ H.
pose proof deduction_andp_elim2 _ _ _ H.
pose proof deduction_andp_elim1 _ _ _ H0.
pose proof deduction_andp_elim2 _ _ _ H0.
rewrite <- provable_derivable in H1.
rewrite <- provable_derivable in H2.
rewrite <- provable_derivable in H3.
rewrite <- provable_derivable in H4.
apply deduction_andp_intros; rewrite <- provable_derivable.
+
apply orp_proper_impp; auto.
+
Admitted.

Instance iffp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) iffp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
unfold iffp.
rewrite H, H0.
Admitted.

Instance negp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) negp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
unfold negp.
apply impp_proper_iffp; auto.
Admitted.

Instance andp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) andp.
Proof.
AddSequentCalculus.
hnf; intros x1 x2 ?.
hnf; intros y1 y2 ?.
rewrite provable_derivable.
rewrite <- !deduction_theorem.
apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H.
apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H0.
pose proof derivable_assum1 empty_context (x1 && y1).
pose proof deduction_andp_elim1 _ _ _ H1.
pose proof deduction_andp_elim2 _ _ _ H1.
pose proof deduction_modus_ponens _ _ _ H2 H.
pose proof deduction_modus_ponens _ _ _ H3 H0.
apply deduction_andp_intros; auto.
