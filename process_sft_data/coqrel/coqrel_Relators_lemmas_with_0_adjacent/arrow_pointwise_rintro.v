Require Export RelDefinitions.
Require Import RelClasses.
Require Import Coq.Lists.List.
Definition arrow_pointwise_rel A {B1 B2}: rel B1 B2 -> rel (A -> B1) (A -> B2) := fun RB f g => forall a, RB (f a) (g a).
Arguments arrow_pointwise_rel A%type {B1%type B2%type} RB%rel _ _.
Notation "- ==> R" := (arrow_pointwise_rel _ R) (at level 55, right associativity) : rel_scope.
Global Instance arrow_pointwise_subrel {A B1 B2}: Monotonic (@arrow_pointwise_rel A B1 B2) (subrel ++> subrel).
Proof.
firstorder.
Global Instance arrow_pointwise_subrel_params: Params (@arrow_pointwise_rel) 3 := { }.
Hint Extern 0 (RIntro _ (- ==> _) _ _) => eapply arrow_pointwise_rintro : typeclass_instances.
Hint Extern 1 (RElim (- ==> _) _ _ _ _) => eapply arrow_pointwise_relim : typeclass_instances.
Hint Extern 1 (Reflexive (- ==> _)) => eapply arrow_pointwise_refl : typeclass_instances.
Global Instance arrow_pointwise_rel_compose {T} `(RCompose) : RCompose (A := T -> A) (- ==> RAB) (- ==> RBC) (- ==> RAC).
Proof.
firstorder.
Definition forall_pointwise_rel {V: Type} {FV1 FV2: V -> Type}: (forall v, rel (FV1 v) (FV2 v)) -> rel (forall v, FV1 v) (forall v, FV2 v) := fun FE f g => forall v, FE v (f v) (g v).
Arguments forall_pointwise_rel {V%type FV1%type FV2%type} FE%rel _ _.
Notation "'forallr' - @ v : V , FE" := (forall_pointwise_rel (V := V) (fun v => FE)) (v ident, at level 200).
Notation "'forallr' - @ v , FE" := (forall_pointwise_rel (fun v => FE)) (v ident, at level 200).
Notation "'forallr' - : V , FE" := (forall_pointwise_rel (V := V) (fun _ => FE)) (at level 200).
Notation "'forallr' - , FE" := (forall_pointwise_rel (fun _ => FE)) (at level 200).
Hint Extern 0 (RIntro _ (forall_pointwise_rel _) _ _) => eapply forall_pointwise_rintro : typeclass_instances.
Hint Extern 1 (RElim (forall_pointwise_rel _) _ _ _ _) => eapply forall_pointwise_relim : typeclass_instances.
Definition forallp_rel {V1 V2} (E: rel V1 V2) {FV1: V1->Type} {FV2: V2->Type}: (forall v1 v2, rel (FV1 v1) (FV2 v2)) -> rel (forall v1, FV1 v1) (forall v2, FV2 v2) := fun FE f g => forall v1 v2, E v1 v2 -> FE v1 v2 (f v1) (g v2).
Arguments forallp_rel {V1%type V2%type} E%rel {FV1%type FV2%type} FE%rel _ _.
Notation "'forallr' v1 v2 : E , R" := (forallp_rel E (fun v1 v2 => R)) (at level 200, v1 ident, v2 ident, right associativity) : rel_scope.
Hint Extern 0 (RIntro _ (forallp_rel _ _) _ _) => eapply forallp_rintro : typeclass_instances.
Hint Extern 1 (RElim (forallp_rel _ _) _ _ _ _) => eapply forallp_relim : typeclass_instances.
Definition set_le {A B} (R: rel A B): rel (A -> Prop) (B -> Prop) := fun sA sB => forall a, sA a -> exists b, sB b /\ R a b.
Global Instance set_le_subrel {A B}: Monotonic (@set_le A B) (subrel ++> subrel).
Proof.
intros R1 R2 HR sA sB Hs.
intros x Hx.
destruct (Hs x) as (y & Hy & Hxy); eauto.
Global Instance set_le_subrel_params: Params (@set_le) 3 := { }.
Hint Extern 1 (Reflexive (set_le _)) => eapply set_le_refl : typeclass_instances.
Global Instance set_le_compose `(RCompose) : RCompose (set_le RAB) (set_le RBC) (set_le RAC).
Proof.
intros sa sb sc Hsab Hsbc a Ha.
edestruct Hsab as (b & Hb & Hab); eauto.
edestruct Hsbc as (c & Hc & Hbc); eauto.
Definition set_ge {A B} (R: rel A B): rel (A -> Prop) (B -> Prop) := fun sA sB => forall b, sB b -> exists a, sA a /\ R a b.
Global Instance set_ge_subrel {A B}: Monotonic (@set_ge A B) (subrel ++> subrel).
Proof.
firstorder.
Global Instance set_ge_subrel_params: Params (@set_ge) 3 := { }.
Hint Extern 1 (Reflexive (set_ge _)) => eapply set_ge_refl : typeclass_instances.
Global Instance set_ge_compose `(RCompose) : RCompose (set_ge RAB) (set_ge RBC) (set_ge RAC).
Proof.
intros sa sb sc Hsab Hsbc c Hc.
edestruct Hsbc as (b & Hb & Hbc); eauto.
edestruct Hsab as (a & Ha & Hab); eauto.
Inductive Empty_set_rel: rel Empty_set Empty_set := .
Inductive unit_rel: rel unit unit := tt_rel: Proper unit_rel tt.
Global Existing Instance tt_rel.
Inductive sum_rel {A1 A2 B1 B2} RA RB: rel (A1 + B1)%type (A2 + B2)%type := | inl_rel_def: (RA ++> sum_rel RA RB)%rel (@inl A1 B1) (@inl A2 B2) | inr_rel_def: (RB ++> sum_rel RA RB)%rel (@inr A1 B1) (@inr A2 B2).
Infix "+" := sum_rel : rel_scope.
Global Instance inl_rel: Monotonic (@inl) (forallr RA, forallr RB, RA ++> RA + RB).
Proof.
repeat intro; apply inl_rel_def; assumption.
Global Instance inr_rel: Monotonic (@inr) (forallr RA, forallr RB, RB ++> RA + RB).
Proof.
repeat intro; apply inr_rel_def; assumption.
Global Instance sum_subrel {A1 A2 B1 B2}: Monotonic (@sum_rel A1 A2 B1 B2) (subrel ++> subrel ++> subrel).
Proof.
intros RA1 RA2 HRA RB1 RB2 HRB.
intros x1 x2 Hx.
destruct Hx; constructor; eauto.
Global Instance sum_subrel_params: Params (@sum_rel) 4 := { }.
Hint Extern 2 (Reflexive (_ + _)) => eapply sum_rel_refl : typeclass_instances.
Hint Extern 2 (Coreflexive (_ + _)) => eapply sum_rel_corefl : typeclass_instances.
Hint Extern 2 (Transitive (_ + _)) => eapply sum_rel_trans : typeclass_instances.
Hint Extern 2 (Symmetric (_ + _)) => eapply sum_rel_sym : typeclass_instances.
Hint Extern 2 (PreOrder (_ + _)) => eapply sum_rel_preorder : typeclass_instances.
Definition prod_rel {A1 A2 B1 B2} RA RB: rel (A1 * B1)%type (A2 * B2)%type := fun x1 x2 => RA (fst x1) (fst x2) /\ RB (snd x1) (snd x2).
Infix "*" := prod_rel : rel_scope.
Global Instance pair_rel: Monotonic (@pair) (forallr RA, forallr RB, RA ++> RB ++> RA * RB).
Proof.
intros A1 A2 RA B1 B2 RB a1 a2 Ha b1 b2 Hb.
red.
eauto.
Global Instance fst_rel: Monotonic (@fst) (forallr RA, forallr RB, RA * RB ==> RA).
Proof.
intros A1 A2 RA B1 B2 RB.
intros x1 x2 [Ha Hb].
assumption.
Global Instance snd_rel: Monotonic (@snd) (forallr RA, forallr RB, RA * RB ==> RB).
Proof.
intros A1 A2 RA B1 B2 RB.
intros x1 x2 [Ha Hb].
assumption.
Global Instance prod_subrel {A1 A2 B1 B2}: Monotonic (@prod_rel A1 A2 B1 B2) (subrel ++> subrel ++> subrel).
Proof.
firstorder.
Global Instance prod_subrel_params: Params (@prod_rel) 4 := { }.
Global Instance prod_rdestruct {A1 B1 A2 B2} (RA: rel A1 A2) (RB: rel B1 B2): RDestruct (RA * RB)%rel (fun P => forall a1 a2 b1 b2, RA a1 a2 -> RB b1 b2 -> P (a1, b1) (a2, b2)).
Proof.
intros [a1 b1] [a2 b2] [Ha Hb] P HP.
firstorder.
Hint Extern 2 (Reflexive (_ * _)) => eapply prod_rel_refl : typeclass_instances.
Hint Extern 2 (Coreflexive (_ * _)) => eapply prod_rel_corefl : typeclass_instances.
Hint Extern 2 (Transitive (_ * _)) => eapply prod_rel_trans : typeclass_instances.
Hint Extern 2 (Symmetric (_ * _)) => eapply prod_rel_sym : typeclass_instances.
Hint Extern 2 (PreOrder (_ * _)) => eapply prod_rel_preorder : typeclass_instances.
Inductive option_rel {A1 A2} (RA: rel A1 A2): rel (option A1) (option A2) := | Some_rel_def: (RA ++> option_rel RA)%rel (@Some A1) (@Some A2) | None_rel_def: option_rel RA (@None A1) (@None A2).
Global Instance Some_rel: Monotonic (@Some) (forallr R @ A1 A2 : rel, R ++> option_rel R).
Proof.
exact @Some_rel_def.
Global Instance None_rel: Monotonic (@None) (forallr R, option_rel R).
Proof.
exact @None_rel_def.
Global Instance option_subrel {A1 A2}: Monotonic (@option_rel A1 A2) (subrel ++> subrel).
Proof.
intros RA1 RA2 HRA.
intros x1 x2 Hx.
destruct Hx; constructor; eauto.
Global Instance option_subrel_params: Params (@option_rel) 3 := { }.
Hint Extern 1 (Reflexive (option_rel _)) => eapply option_rel_refl : typeclass_instances.
Global Instance option_map_rel: Monotonic (@option_map) (forallr RA, forallr RB, (RA ++> RB) ++> option_rel RA ++> option_rel RB).
Proof.
intros A1 A2 RA B1 B2 RB f g Hfg x y Hxy.
destruct Hxy; constructor; eauto.
Inductive list_rel {A1 A2} (R: rel A1 A2): rel (list A1) (list A2) := | nil_rel_def: (list_rel R) (@nil A1) (@nil A2) | cons_rel_def: (R ++> list_rel R ++> list_rel R)%rel (@cons A1) (@cons A2).
Global Instance nil_rel: Monotonic (@nil) (forallr R, list_rel R).
Proof.
exact @nil_rel_def.
Global Instance cons_rel: Monotonic (@cons) (forallr R, R ++> list_rel R ++> list_rel R).
Proof.
exact @cons_rel_def.
Global Instance list_subrel {A1 A2}: Monotonic (@list_rel A1 A2) (subrel ++> subrel).
Proof.
intros R S HRS x y.
red in HRS.
induction 1; constructor; eauto.
Global Instance list_subrel_params: Params (@list_rel) 3 := { }.
Hint Extern 1 (Reflexive (list_rel _)) => eapply list_rel_refl : typeclass_instances.
Hint Extern 1 (Coreflexive (list_rel _)) => eapply list_rel_corefl : typeclass_instances.
Hint Extern 1 (Symmetric (list_rel _)) => eapply list_rel_sym : typeclass_instances.
Hint Extern 1 (Transitive (list_rel _)) => eapply list_rel_trans : typeclass_instances.
Global Instance length_rel: Monotonic (@length) (forallr R : rel, list_rel R ++> eq).
Proof.
induction 1; simpl; congruence.
Global Instance app_rel: Monotonic (@app) (forallr R : rel, list_rel R ++> list_rel R ++> list_rel R).
Proof.
intros A1 A2 R l1 l2 Hl.
induction Hl as [ | x1 x2 Hx l1 l2 Hl IHl]; simpl.
-
firstorder.
-
constructor; eauto.
Global Instance map_rel: Monotonic (@map) (forallr RA, forallr RB, (RA ++> RB) ++> list_rel RA ++> list_rel RB).
Proof.
intros A1 A2 RA B1 B2 RB f g Hfg l1 l2 Hl.
induction Hl; constructor; eauto.
Global Instance fold_right_rel: Monotonic (@fold_right) (forallr RA, forallr RB, (RB ++> RA ++> RA) ++> RA ++> list_rel RB ++> RA).
Proof.
intros A1 A2 RA B1 B2 RB f g Hfg a1 a2 Ha l1 l2 Hl.
induction Hl; simpl; eauto.
eapply Hfg; eauto.
Global Instance fold_left_rel: Monotonic (@fold_left) (forallr RA, forallr RB, (RA ++> RB ++> RA) ++> list_rel RB ++> RA ++> RA).
Proof.
intros A1 A2 RA B1 B2 RB f g Hfg l1 l2 Hl.
induction Hl; simpl.
-
firstorder.
-
intros a1 a2 Ha.
eapply IHHl.
eapply Hfg; assumption.
Hint Extern 1 (RStep _ (_ -> _)) => eapply fold_impl_rstep : typeclass_instances.
Global Instance all_monotonic {A}: Monotonic (@all A) ((- ==> impl) ++> impl).
Proof.
intros P Q HPQ H x.
apply HPQ.
apply H.
Global Instance all_monotonic_params: Params (@all) 1 := { }.
Global Instance ex_monotonic A: Monotonic (@ex A) ((- ==> impl) ++> impl).
Proof.
intros P Q HPQ [x Hx].
exists x.
apply HPQ.
assumption.
Global Instance ex_monotonic_params: Params (@ex) 1 := { }.
Global Instance and_monotonic: Monotonic (@and) (impl ++> impl ++> impl).
Proof.
intros P1 P2 HP Q1 Q2 HQ [HP1 HQ1].
eauto.
Global Instance or_monotonic: Monotonic (@or) (impl ++> impl ++> impl).
Proof.
intros P1 P2 HP Q1 Q2 HQ [HP1|HQ1]; eauto.

Lemma arrow_pointwise_rintro {A B1 B2} (R: rel B1 B2) f g: RIntro (forall x: A, R (f x) (g x)) (- ==> R) f g.
Proof.
firstorder.
