Require Export RelDefinitions.
Require Import RelClasses.
Require Import Relators.
Definition rel_union {A B} (R1 R2: rel A B): rel A B := fun x y => R1 x y \/ R2 x y.
Arguments rel_union {_ _} R1%rel R2%rel _ _.
Infix "\/" := rel_union : rel_scope.
Global Instance rel_union_subrel {A B}: Monotonic (@rel_union A B) (subrel ++> subrel ++> subrel).
Proof.
clear.
firstorder.
Global Instance rel_union_subrel_params: Params (@rel_union) 4 := { }.
Hint Extern 0 (RExists _ (_ \/ _) _ _) => eapply rel_union_rexists_l : typeclass_instances.
Hint Extern 0 (RExists _ (_ \/ _) _ _) => eapply rel_union_rexists_r : typeclass_instances.
Hint Extern 0 (RExists _ subrel _ (_ \/ _)%rel) => eapply rel_union_subrel_rexists_l : typeclass_instances.
Hint Extern 0 (RExists _ subrel _ (_ \/ _)%rel) => eapply rel_union_subrel_rexists_r : typeclass_instances.
Hint Extern 2 (RIntro _ subrel (_ \/ _)%rel _) => eapply rel_union_lub : typeclass_instances.
Hint Extern 1 (Reflexive (_ \/ _)) => eapply rel_union_refl_l : typeclass_instances.
Hint Extern 1 (Reflexive (_ \/ _)) => eapply rel_union_refl_r : typeclass_instances.
Hint Extern 1 (Coreflexive (_ \/ _)) => eapply rel_union_corefl : typeclass_instances.
Hint Extern 1 (Symmetric (_ \/ _)) => eapply rel_union_sym : typeclass_instances.
Definition rel_inter {A B} (R1 R2: rel A B): rel A B := fun x y => R1 x y /\ R2 x y.
Arguments rel_inter {_ _} R1%rel R2%rel _ _.
Infix "/\" := rel_inter : rel_scope.
Global Instance rel_inter_subrel {A B}: Monotonic (@rel_inter A B) (subrel ++> subrel ++> subrel).
Proof.
clear.
firstorder.
Global Instance rel_inter_params: Params (@rel_inter) 4 := { }.
Hint Extern 0 (RExists _ (_ /\ _) _ _) => eapply rel_inter_rexists : typeclass_instances.
Hint Extern 0 (RExists _ subrel (_ /\ _)%rel _) => eapply rel_inter_subrel_rexists_l : typeclass_instances.
Hint Extern 0 (RExists _ subrel (_ /\ _)%rel _) => eapply rel_inter_subrel_rexists_r : typeclass_instances.
Hint Extern 2 (RIntro _ subrel _ (_ /\ _)%rel) => eapply rel_inter_glb : typeclass_instances.
Hint Extern 2 (Reflexive (_ /\ _)) => eapply rel_inter_refl : typeclass_instances.
Hint Extern 1 (Coreflexive (_ /\ _)) => eapply rel_inter_corefl_l : typeclass_instances.
Hint Extern 1 (Coreflexive (_ /\ _)) => eapply rel_inter_corefl_r : typeclass_instances.
Hint Extern 2 (Transitive (_ /\ _)) => eapply rel_inter_trans : typeclass_instances.
Hint Extern 2 (Symmetric (_ /\ _)) => eapply rel_inter_sym : typeclass_instances.
Global Instance rel_inter_flip_sym {A} (R: rel A A): Symmetric (R /\ flip R).
Proof.
intros x y [Hxy Hyx].
split; assumption.
Hint Extern 60 (RStep _ (subrel _ (flip _))) => eapply subrel_sym_flip : typeclass_instances.
Definition rel_impl {A B} (R1 R2: rel A B): rel A B := fun x y => R1 x y -> R2 x y.
Global Instance rel_impl_subrel {A B}: Monotonic (@rel_impl A B) (subrel --> subrel ++> subrel).
Proof.
firstorder.
Global Instance rel_impl_subrel_params: Params (@rel_impl) 4 := { }.
Hint Extern 0 (RIntro _ (rel_impl _ _) _ _) => eapply rel_impl_rintro : typeclass_instances.
Hint Extern 0 (RElim (rel_impl _ _) _ _ _ _) => eapply rel_impl_relim : typeclass_instances.
Definition rel_bot {A B}: rel A B := fun x y => False.
Notation "⊥" := rel_bot : rel_scope.
Hint Extern 0 (Related ⊥%rel _ _) => eapply rel_bot_subrel : typeclass_instances.
Hint Extern 0 (RElim ⊥ _ _ _ _) => eapply rel_bot_relim : typeclass_instances.
Definition rel_top {A B}: rel A B := fun x y => True.
Notation "⊤" := rel_top : rel_scope.
Hint Extern 0 (RIntro _ ⊤ _ _) => eapply rel_top_rintro : typeclass_instances.
Global Instance rel_top_equiv {A}: @Equivalence A ⊤.
Proof.
repeat constructor.
Definition eqrel {A B}: rel (rel A B) (rel A B) := (subrel /\ flip subrel)%rel.
Arguments eqrel {_ _} RA%rel RB%rel.
Global Instance eqrel_equivalence A B: Equivalence (@eqrel A B).
Proof.
unfold eqrel.
split; typeclasses eauto.
Global Instance eqrel_subrel A B: Related (@eqrel A B) (@subrel A B) subrel.
Proof.
firstorder.
Definition rel_compose {A B C} (RAB: rel A B) (RBC: rel B C): rel A C := fun x z => exists y, RAB x y /\ RBC y z.
Hint Unfold rel_compose : core.
Global Instance rel_compose_subrel {A B C}: Monotonic (@rel_compose A B C) (subrel ++> subrel ++> subrel).
Proof.
firstorder.
Global Instance rel_compose_eqrel {A B C}: Monotonic (@rel_compose A B C) (eqrel ==> eqrel ==> eqrel).
Proof.
firstorder.
Global Instance rel_compose_params: Params (@rel_compose) 4 := { }.
Global Instance rel_compose_rcompose {A B C} (RAB : rel A B) (RBC : rel B C) : RCompose RAB RBC (rel_compose RAB RBC).
Proof.
firstorder.
Global Instance rel_compose_rdecompose {A B C} (RAB : rel A B) (RBC : rel B C) : RDecompose RAB RBC (rel_compose RAB RBC).
Proof.
firstorder.
Global Instance rcompose_subrel `(RCompose) : Related (rel_compose RAB RBC) RAC subrel.
Proof.
firstorder.
Global Instance rdecompose_subrel `(RDecompose) : Related RAC (rel_compose RAB RBC) subrel.
Proof.
firstorder.
Definition rel_pull {A B A' B'} f g (R: rel A' B'): rel A B := fun x y => R (f x) (g y).
Notation "R @@ ( f , g )" := (rel_pull f g R) (at level 30, right associativity) : rel_scope.
Notation "R @@ f" := (rel_pull f f R) (at level 30, right associativity) : rel_scope.
Notation "R @@ ( f )" := (rel_pull f f R) (at level 30, right associativity) : rel_scope.
Global Instance rel_pull_subrel {A B A' B'} (f: A -> A') (g: B -> B'): Monotonic (rel_pull f g) (subrel ++> subrel).
Proof.
firstorder.
Global Instance rel_pull_subrel_params: Params (@rel_pull) 3 := { }.
Hint Extern 1 (Reflexive (rel_pull _ _ _)) => eapply rel_pull_refl : typeclass_instances.
Hint Extern 1 (Symmetric (rel_pull _ _ _)) => eapply rel_pull_sym : typeclass_instances.
Hint Extern 1 (RCompose _ _ (rel_pull _ _ _)) => eapply rel_pull_rcompose : typeclass_instances.
Hint Extern 60 (RStep _ ((_ @@ (_, _))%rel _ _)) => eapply rel_pull_rintro : typeclass_instances.
Hint Extern 1 (RElim (_ @@ (_, _)) _ _ _ _) => eapply rel_pull_relim : typeclass_instances.
Inductive rel_push {A1 A2 B1 B2} f g (R: rel A1 A2): rel B1 B2 := rel_push_rintro x y: RIntro (R x y) (rel_push f g R) (f x) (g y).
Hint Extern 1 (RIntro _ (rel_push _ _ _) _ _) => eapply rel_push_rintro : typeclass_instances.
Notation "R !! ( f , g )" := (rel_push f g R) (at level 1) : rel_scope.
Notation "R !! f" := (rel_push f f R) (at level 1) : rel_scope.
Notation "R !! ( f )" := (rel_push f f R) (at level 1) : rel_scope.
Global Instance rel_push_subrel {A1 A2 B1 B2} (f: A1 -> B1) (g: A2 -> B2): Proper (subrel ++> subrel) (rel_push f g).
Proof.
intros R1 R2 HR x y Hxy.
destruct Hxy.
rintro; eauto.
Global Instance rel_push_subrel_params: Params (@rel_push) 3 := { }.
Hint Extern 1 (Coreflexive (_ !! _)) => eapply rel_push_corefl : typeclass_instances.
Hint Extern 1 (RExists _ (_ !! fst) _ _) => eapply rel_push_fst_rexists : typeclass_instances.
Hint Extern 1 (RExists _ (_ !! snd) _ _) => eapply rel_push_snd_rexists : typeclass_instances.
Definition curry {A B C} (f: A * B -> C): A -> B -> C := fun a b => f (a, b).
Definition uncurry {A B C} (f: A -> B -> C): A * B -> C := fun ab => match ab with (a, b) => f a b end.
Definition rel_curry {A1 B1 C1 A2 B2 C2} (R: rel (A1*B1->C1) (A2*B2->C2)) := (R @@ uncurry)%rel.
Definition rel_uncurry {A1 B1 C1 A2 B2 C2} (R: rel (A1->B1->C1) (A2->B2->C2)) := (R @@ curry)%rel.
Notation "% R" := (rel_curry R) (at level 55, right associativity) : rel_scope.
Class UnfoldUncurry {A} (before: A) (after: A) := unfold_uncurry_before_after: before = after.
Ltac unfold_uncurry := match goal with | |- context C[uncurry ?f ?p] => is_evar p; let T := type of p in let Av := fresh in evar (Av: Type); let A := eval red in Av in clear Av; let Bv := fresh in evar (Bv: Type); let B := eval red in Bv in clear Bv; unify T (prod A B)%type; let av := fresh in evar (av : A); let a := eval red in av in clear av; let bv := fresh in evar (bv : B); let b := eval red in bv in clear bv; let G := context C[f a b] in unify p (a, b); change G end.
Hint Extern 1 (UnfoldUncurry ?P ?Q) => repeat unfold_uncurry; constructor : typeclass_instances.
Hint Extern 60 (RStep _ ((% _)%rel _ _)) => eapply rel_pull_rintro : typeclass_instances.
Hint Extern 1 (RElim (% _) _ _ _ _) => eapply rel_curry_relim : typeclass_instances.
Inductive req {A} (a: A): rel A A := req_intro: req a a a.
Hint Extern 0 (RIntro _ (req _) _ _) => eapply req_rintro : typeclass_instances.
Hint Extern 0 (Coreflexive (req _)) => eapply req_corefl : typeclass_instances.
Definition lsat {A B} (P: A -> Prop): rel A B := fun x y => P x.
Global Instance lsat_subrel A B: Monotonic (@lsat A B) ((- ==> impl) ++> subrel).
Proof.
firstorder.
Global Instance lsat_subrel_params: Params (@lsat) 3 := { }.
Definition rsat {A B} (P: B -> Prop): rel A B := fun x y => P y.
Global Instance rsat_subrel A B: Monotonic (@rsat A B) ((- ==> impl) ++> subrel).
Proof.
firstorder.
Global Instance rsat_subrel_params: Params (@rsat) 3 := { }.
Inductive psat {A} (I: A -> Prop) (x: A): A -> Prop := psat_intro: I x -> psat I x x.
Global Instance psat_subrel A: Monotonic (@psat A) ((- ==> impl) ++> subrel).
Proof.
intros P Q HPQ x _ [Hx].
constructor.
apply HPQ.
assumption.
Global Instance psat_subrel_params: Params (@psat) 3 := { }.
Hint Extern 0 (Coreflexive (psat _)) => eapply psat_corefl : typeclass_instances.
Definition rel_all {A B C} (R: C -> rel A B): rel A B := fun x y => forall c, R c x y.
Notation "'rforall' x .. y , p" := (rel_all (fun x => .. (rel_all (fun y => p%rel)) .. )) (at level 200, x binder, right associativity) : rel_scope.
Hint Extern 0 (RIntro _ (rel_all _) _ _) => eapply rel_all_rintro : typeclass_instances.
Hint Extern 1 (RElim (rel_all _) _ _ _ _) => eapply rel_all_relim; eexists : typeclass_instances.
Definition rel_ex {A B C} (R: C -> rel A B): rel A B := fun x y => exists c, R c x y.
Notation "'rexists' x .. y , p" := (rel_ex (fun x => .. (rel_ex (fun y => p%rel)) ..)) (at level 200, x binder, right associativity) : rel_scope.
Hint Extern 0 (RExists _ (rel_ex _) _ _) => eapply rel_ex_rintro : typeclass_instances.
Hint Extern 1 (RElim (rel_ex _) _ _ _ _) => eapply rel_ex_relim : typeclass_instances.
Definition rel_incr {W A B} (acc: rel W W) (R: W -> rel A B): W -> rel A B := fun w a b => exists w', acc w w' /\ R w' a b.
Global Instance rel_incr_subrel {W A B} acc: Transitive acc -> Monotonic (@rel_incr W A B acc) ((- ==> subrel) ++> acc --> subrel).
Proof.
intros Hacc R1 R2 HR w1 w2 Hw a b (w1' & Hw1' & Hab).
eexists; split.
-
transitivity w1; eassumption.
-
apply HR.
assumption.
Global Instance rel_incr_subrel_params: Params (@rel_incr) 4 := { }.
Hint Extern 0 (RExists _ (rel_incr _ _ _) _ _) => eapply rel_incr_rintro : typeclass_instances.
Hint Extern 2 (RDestruct (rel_incr _ _ _) _) => eapply rel_incr_rdestruct; intro; eexists; split : typeclass_instances.

Lemma rel_push_fst_rexists {A1 A2 B1 B2} (x1:A1) (x2:A2) (y1:B1) (y2:B2) R: RExists (R (x1, y1) (x2, y2)) (R !! fst) x1 x2.
Proof.
intros H.
change x1 with (fst (x1, y1)).
change x2 with (fst (x2, y2)).
rintro.
Admitted.

Lemma rel_push_snd_rexists {A1 A2 B1 B2} (x1:A1) (x2:A2) (y1:B1) (y2:B2) R: RExists (R (x1, y1) (x2, y2)) (R !! snd) y1 y2.
Proof.
intros H.
change y1 with (snd (x1, y1)).
change y2 with (snd (x2, y2)).
rintro.
Admitted.

Lemma rel_curry_relim {A1 B1 C1 A2 B2 C2} R f g P Q Q': @RElim (A1 * B1 -> C1) (A2 * B2 -> C2) R (uncurry f) (uncurry g) P Q -> UnfoldUncurry Q Q' -> @RElim (A1 -> B1 -> C1) (A2 -> B2 -> C2) (% R) f g P Q'.
Proof.
unfold UnfoldUncurry.
intros; subst.
Admitted.

Lemma req_rintro {A} (a: A): RIntro True (req a) a a.
Proof.
Admitted.

Lemma req_corefl {A} (a: A): Coreflexive (req a).
Proof.
destruct 1.
Admitted.

Lemma psat_corefl {A} (I: A -> Prop): Coreflexive (psat I).
Proof.
intros x _ [_].
Admitted.

Lemma rel_all_rintro {A B C} (R: C -> rel A B) m n: RIntro (forall c : C, R c m n) (rel_all R) m n.
Proof.
Admitted.

Lemma rel_all_relim {A B C} (R: C -> rel A B) x y P Q: (exists c, RElim (R c) x y P Q) -> RElim (rel_all R) x y P Q.
Proof.
Admitted.

Lemma rel_ex_rintro {A B C} (R: C -> rel A B) c m n: RExists (R c m n) (rel_ex R) m n.
Proof.
Admitted.

Lemma rel_ex_relim {A B C} (R: C -> rel A B) x y P Q: (forall c, RElim (R c) x y P Q) -> RElim (rel_ex R) x y P Q.
Proof.
Admitted.

Lemma rel_incr_rdestruct {W A B} acc R w T: (forall w, exists Tw, RDestruct (R w) Tw /\ Convertible (T w) Tw) -> RDestruct (@rel_incr W A B acc R w) (fun P => forall w', acc w w' -> Delay.unpack (T w' P)).
Proof.
clear.
intros HR m n (w' & Hw' & Hmn) P H.
destruct (HR w') as (Tw & HRw' & HTw).
eapply rdestruct; eauto.
destruct HTw.
Admitted.

Lemma rel_incr_rintro {W A B} (acc: rel W W) (R: W -> rel A B) w w' m n: RExists (R w' m n /\ acc w w') (rel_incr acc R w) m n.
Proof.
firstorder.
