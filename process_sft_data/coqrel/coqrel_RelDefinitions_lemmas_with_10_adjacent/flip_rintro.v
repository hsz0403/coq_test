Require Export Coq.Program.Basics.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.Morphisms.
Require Setoid.
Require Export Delay.
Class NotEvar {A} (x: A).
Hint Extern 1 (NotEvar ?x) => not_evar x; constructor : typeclass_instances.
Class Unconvertible {A B} (a: A) (b: B) := unconvertible : unit.
Ltac unconvertible a b := first [ unify a b with typeclass_instances; fail 1 | exact tt ].
Hint Extern 1 (Unconvertible ?a ?b) => unconvertible a b : typeclass_instances.
Class Convertible {A} (x y: A) := convertible: x = y.
Hint Extern 1 (Convertible ?x ?y) => eapply eq_refl : typeclass_instances.
Class Once P := once : P.
Hint Extern 1 (Once ?P) => red; once typeclasses eauto : typeclass_instances.
Definition rel (A1 A2: Type) := A1 -> A2 -> Prop.
Declare Scope rel_scope.
Delimit Scope rel_scope with rel.
Bind Scope rel_scope with rel.
Bind Scope rel_scope with Relation_Definitions.relation.
Class RStep (P Q: Prop) := rstep: P -> Q.
Ltac rstep := lazymatch goal with | |- ?Q => apply (rstep (Q := Q)); Delay.split_conjunction end.
Class RAuto (Q: Prop) := rauto : Q.
Ltac rauto := lazymatch goal with | |- ?Q => apply (rauto (Q := Q)); Delay.split_conjunction end.
Class RAutoSubgoals (P: Prop) := rauto_subgoals : P.
Global Instance rauto_rstep P Q: Once (RStep P Q) -> RAutoSubgoals P -> RAuto Q.
Proof.
firstorder.
Ltac rauto_split := red; Delay.split_conjunction; lazymatch goal with | |- ?Q => change (RAuto Q) end.
Hint Extern 1 (RAutoSubgoals _) => rauto_split : typeclass_instances.
Hint Extern 1000 (RAuto _) => red; solve [ delay ] : typeclass_instances.
Ltac no_evars t := lazymatch t with | ?f ?x => no_evars f; no_evars x | ?m => not_evar m end.
Hint Extern 10 (RStep _ (?R ?x ?x)) => no_evars R; eapply reflexivity_rstep : typeclass_instances.
Class RIntro {A B} (P: Prop) (R: rel A B) (m: A) (n: B): Prop := rintro: P -> R m n.
Arguments RIntro {A%type B%type} P%type R%rel m n.
Ltac rintro := lazymatch goal with | |- ?R ?m ?n => apply (rintro (R:=R) (m:=m) (n:=n)); Delay.split_conjunction end.
Global Instance rintro_rstep: forall `(RIntro), RStep P (R m n) | 20.
Proof.
firstorder.
Class RExists {A B} (P: Prop) (R: rel A B) (m: A) (n: B): Prop := rexists: P -> R m n.
Arguments RExists {A%type B%type} P%type R%rel m n.
Ltac reexists := lazymatch goal with | |- ?R ?m ?n => apply (rexists (R:=R) (m:=m) (n:=n)); Delay.split_conjunction end.
Global Instance rexists_rstep {A B} P R (m:A) (n:B): RExists P R m n -> NonDelayed (RAutoSubgoals P) -> RStep True (R m n) | 70.
Proof.
firstorder.
Class RElim {A B} (R: rel A B) (m: A) (n: B) (P Q: Prop): Prop := relim: R m n -> P -> Q.
Arguments RElim {A%type B%type} R%rel m n P%type Q%type.
Ltac relim H := lazymatch goal with | |- ?Q => apply (relim (Q:=Q) H) (* ^ XXX split_conjunction? *) end.
Global Instance relim_base {A B} (R: rel A B) m n: RElim R m n True (R m n) | 10.
Proof.
firstorder.
Class RDestruct {A B: Type} (R: rel A B) (T: rel A B -> Prop) := rdestruct m n: R m n -> forall P, T P -> P m n.
Class Related {A B} (f: A) (g: B) (R: rel A B) := related: R f g.
Arguments Related {A%type B%type} _ _ R%rel.
Notation "'@' 'Monotonic' T m R" := (@Related T T m m R%rel) (at level 10, T at next level, R at next level, m at next level).
Notation Monotonic m R := (Related m m R%rel).
Hint Extern 1 (RStep _ (Related _ _ _)) => eapply unfold_monotonic_rstep : typeclass_instances.
Definition subrel {A B}: rel (rel A B) (rel A B) := fun R1 R2 => forall x y, R1 x y -> R2 x y.
Arguments subrel {A%type B%type} R1%rel R2%rel.
Global Instance subrel_preorder A B: @PreOrder (rel A B) subrel.
Proof.
split; firstorder.
Global Instance eq_subrel {A} (R: rel A A): Reflexive R -> Related eq R subrel.
Proof.
intros HR x y H.
subst.
reflexivity.
Instance subrel_impl_relim {A B} (R1 R2 : rel A B) x1 x2 y1 y2 P Q: RElim impl (R1 x1 y1) (R2 x2 y2) P Q -> RElim subrel R1 R2 (x1 = x2 /\ y1 = y2 /\ P) Q.
Proof.
cbv.
firstorder.
subst.
eauto.
Definition arrow_rel {A1 A2 B1 B2}: rel A1 A2 -> rel B1 B2 -> rel (A1 -> B1) (A2 -> B2) := fun RA RB f g => forall x y, RA x y -> RB (f x) (g y).
Arguments arrow_rel {A1%type A2%type B1%type B2%type} RA%rel RB%rel _ _.
Notation "RA ==> RB" := (arrow_rel RA RB) (at level 55, right associativity) : rel_scope.
Notation "RA ++> RB" := (arrow_rel RA RB) (at level 55, right associativity) : rel_scope.
Notation "RA --> RB" := (arrow_rel (flip RA) RB) (at level 55, right associativity) : rel_scope.
Global Instance arrow_subrel {A1 A2 B1 B2}: Monotonic (@arrow_rel A1 A2 B1 B2) (subrel --> subrel ++> subrel).
Proof.
firstorder.
Global Instance arrow_subrel_params: Params (@arrow_rel) 4 := { }.
Hint Extern 0 (RIntro _ (_ ++> _) _ _) => eapply arrow_rintro : typeclass_instances.
Hint Extern 1 (RElim (_ ++> _) _ _ _ _) => eapply arrow_relim : typeclass_instances.
Definition forall_rel {V1 V2} {E: V1->V2->Type} {FV1: V1->Type} {FV2: V2->Type}: (forall v1 v2, E v1 v2 -> rel (FV1 v1) (FV2 v2)) -> rel (forall v1, FV1 v1) (forall v2, FV2 v2) := fun FE f g => forall v1 v2 (e: E v1 v2), FE v1 v2 e (f v1) (g v2).
Arguments forall_rel {V1%type V2%type E%type FV1%type FV2%type} FE%rel _ _.
Notation "'forallr' e @ v1 v2 : E , R" := (forall_rel (E := E) (fun v1 v2 e => R)) (at level 200, e ident, v1 ident, v2 ident, right associativity) : rel_scope.
Notation "'forallr' e @ v1 v2 , R" := (forall_rel (fun v1 v2 e => R)) (at level 200, e ident, v1 ident, v2 ident, right associativity) : rel_scope.
Notation "'forallr' e : E , R" := (forall_rel (E := E) (fun _ _ e => R)) (at level 200, e ident, right associativity) : rel_scope.
Notation "'forallr' e , R" := (forall_rel (fun _ _ e => R)) (at level 200, e ident, right associativity) : rel_scope.
Hint Extern 0 (RIntro _ (forall_rel _) _ _) => eapply forall_rintro : typeclass_instances.
Hint Extern 1 (RElim (forall_rel _) _ _ _ _) => eapply forall_relim : typeclass_instances.
Global Instance flip_subrel {A B}: Monotonic (@flip A B Prop) (subrel ++> subrel).
Proof.
firstorder.
Global Instance flip_subrel_params: Params (@flip) 3 := { }.
Hint Extern 1 (RIntro _ (flip _) _ _) => eapply flip_rintro : typeclass_instances.
Hint Extern 1 (RElim (flip _) _ _ _ _) => eapply flip_relim : typeclass_instances.
Hint Extern 1 (RDestruct (flip _) _) => eapply flip_rdestruct : typeclass_instances.
Class PolarityResolved {A B} (R: rel A B).
Hint Extern 1 (PolarityResolved ?R) => not_evar R; constructor : typeclass_instances.
Ltac polarity_unresolved R := is_evar R; lazymatch goal with | H : PolarityResolved R |- _ => fail | _ => idtac end.
Hint Extern 1 (RExists _ ?R _ _) => polarity_unresolved R; eapply direct_rexists : typeclass_instances.
Hint Extern 2 (RExists _ ?R _ _) => polarity_unresolved R; eapply flip_rexists : typeclass_instances.

Lemma reflexivity_rstep {A} (R: rel A A) (x: A) : Reflexive R -> RStep True (R x x).
Proof.
Admitted.

Lemma unfold_monotonic_rstep {A B} (R: rel A B) m n: RStep (R m n) (Related m n R).
Proof.
Admitted.

Instance subrel_impl_relim {A B} (R1 R2 : rel A B) x1 x2 y1 y2 P Q: RElim impl (R1 x1 y1) (R2 x2 y2) P Q -> RElim subrel R1 R2 (x1 = x2 /\ y1 = y2 /\ P) Q.
Proof.
cbv.
firstorder.
subst.
Admitted.

Lemma arrow_rintro {A1 A2 B1 B2} (RA: rel A1 A2) (RB: rel B1 B2) f g: RIntro (forall x y, RA x y -> RB (f x) (g y)) (RA ++> RB) f g.
Proof.
Admitted.

Lemma arrow_relim {A1 A2 B1 B2} RA RB f g m n P Q: @RElim B1 B2 RB (f m) (g n) P Q -> @RElim (A1 -> B1) (A2 -> B2) (RA ++> RB) f g (RA m n /\ P) Q.
Proof.
Admitted.

Lemma forall_rintro {V1 V2 E F1 F2} (FE: forall x y, _ -> rel _ _) f g: RIntro (forall u v e, FE u v e (f u) (g v)) (@forall_rel V1 V2 E F1 F2 FE) f g.
Proof.
Admitted.

Lemma forall_relim {V1 V2 E FV1 FV2} R f g v1 v2 e P Q: RElim (R v1 v2 e) (f v1) (g v2) P Q -> RElim (@forall_rel V1 V2 E FV1 FV2 R) f g P Q.
Proof.
Admitted.

Lemma flip_relim {A B} (R: rel A B) m n P Q: RElim R n m P Q -> RElim (flip R) m n P Q.
Proof.
Admitted.

Lemma flip_rdestruct {A B} (R: rel A B) T: RDestruct R T -> RDestruct (flip R) (fun P => T (flip P)).
Proof.
Admitted.

Lemma direct_rexists {A B} (R: rel A B) (m: A) (n: B): RExists (PolarityResolved R -> R m n) R m n.
Proof.
Admitted.

Lemma flip_rexists {A B} (R: rel A B) (Rc: rel B A) (m: A) (n: B): Convertible R (flip Rc) -> RExists (PolarityResolved Rc -> flip Rc m n) R m n.
Proof.
unfold Convertible.
intros; subst.
Admitted.

Lemma flip_rintro {A B} (R: rel A B) m n: RIntro (R n m) (flip R) m n.
Proof.
firstorder.
