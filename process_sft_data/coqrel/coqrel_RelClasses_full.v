Require Export Coq.Classes.RelationClasses.
Require Export RelDefinitions.
Class Coreflexive {A} (R: relation A) := coreflexivity: forall x y, R x y -> x = y.
Global Instance eq_corefl {A}: Coreflexive (@eq A).
Proof.
firstorder.
Qed.
Global Instance subrel_eq {A} (R: relation A): Coreflexive R -> Related R eq subrel.
Proof.
firstorder.
Qed.
Class RCompose {A B C} (RAB : rel A B) (RBC : rel B C) (RAC : rel A C) := rcompose : forall x y z, RAB x y -> RBC y z -> RAC x z.
Ltac rcompose b := lazymatch goal with | |- ?R ?a ?c => apply (rcompose a b c) end.
Ltac ercompose := eapply rcompose.
Global Instance rcompose_transitive {A} (R : relation A) : RCompose R R R -> Transitive R.
Proof.
firstorder.
Qed.
Lemma transitive_rcompose `(Transitive) : RCompose R R R.
Proof.
assumption.
Qed.
Hint Immediate transitive_rcompose : typeclass_instances.
Class RDecompose {A B C} (RAB : rel A B) (RBC : rel B C) (RAC : rel A C) := rdecompose : forall x z, RAC x z -> exists y, RAB x y /\ RBC y z.
Tactic Notation "rdecompose" constr(H) "as" simple_intropattern(p) := lazymatch type of H with | ?R ?a ?b => destruct (rdecompose a b H) as p | _ => fail "Not an applied relation" end.
Tactic Notation "rdecompose" hyp(H) "as" simple_intropattern(p) := lazymatch type of H with | ?R ?a ?b => apply rdecompose in H; destruct H as p | _ => fail "Not an applied relation" end.
Tactic Notation "rdecompose" constr(H) := rdecompose H as (? & ? & ?).
Tactic Notation "rdecompose" hyp(H) := rdecompose H as (? & ? & ?).
Global Instance arrow_refl {A B} (RA : relation A) (RB : relation B) : Coreflexive RA -> Reflexive RB -> Reflexive (RA ++> RB).
Proof.
intros HA HB f a b Hab.
apply coreflexivity in Hab.
subst.
reflexivity.
Qed.
Global Instance arrow_corefl {A B} (RA : relation A) (RB : relation B) : Reflexive RA -> Coreflexive RB -> Coreflexive (RA ++> RB).
Proof.
Abort.
Section ARROW_REL_COMPOSE.
Context {A1 A2 A3} (RA12 : rel A1 A2) (RA23 : rel A2 A3) (RA13 : rel A1 A3).
Context {B1 B2 B3} (RB12 : rel B1 B2) (RB23 : rel B2 B3) (RB13 : rel B1 B3).
Global Instance arrow_rcompose : RDecompose RA12 RA23 RA13 -> RCompose RB12 RB23 RB13 -> RCompose (RA12 ++> RB12) (RA23 ++> RB23) (RA13 ++> RB13).
Proof.
intros HA HB f g h Hfg Hgh a1 a3 Ha.
rdecompose Ha as (a2 & Ha12 & Ha23).
firstorder.
Qed.
Global Instance arrow_rdecompose : RCompose RA12 RA23 RA13 -> RDecompose RB12 RB23 RB13 -> RDecompose (RA12 ++> RB12) (RA23 ++> RB23) (RA13 ++> RB13).
Proof.
Abort.
End ARROW_REL_COMPOSE.