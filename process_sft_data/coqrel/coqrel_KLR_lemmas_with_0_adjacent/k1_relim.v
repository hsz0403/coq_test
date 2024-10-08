Require Export Monotonicity.
Definition klr W A B: Type := W -> rel A B.
Class KripkeFrame (L: Type) (W: Type) := { acc: L -> rel W W; }.
Infix "~>" := (acc tt) (at level 70).
Declare Scope klr_scope.
Delimit Scope klr_scope with klr.
Bind Scope klr_scope with klr.
Inductive klr_sum {WA A1 A2 WB B1 B2} RA RB: klr (WA + WB) (A1 + B1) (A2 + B2) := | klr_inl w a1 a2 : RA w a1 a2 -> klr_sum RA RB (inl w) (inl a1) (inl a2) | klr_inr w b1 b2 : RB w b1 b2 -> klr_sum RA RB (inr w) (inr b1) (inr b2).
Section LIFT.
Context `{kf: KripkeFrame}.
Context {A1 B1 A2 B2 A B: Type}.
Definition k (R: rel A B): klr W A B := fun w => R.
Global Instance k_rel var: Monotonic k (var ++> - ==> var).
Proof.
unfold k; rauto.
Definition k1 RR (R1: klr W A1 B1): klr W A B := fun w => RR (R1 w).
Global Instance k1_rel var1 var: Monotonic k1 ((var1 ++> var) ++> ((- ==> var1) ++> (- ==> var))).
Proof.
unfold k1; rauto.
Definition k2 RR (R1: klr W A1 B1) (R2: klr W A2 B2): klr W A B := fun w => RR (R1 w) (R2 w).
Global Instance k2_rel var1 var2 var: Monotonic k2 ((var1 ++> var2 ++> var) ++> ((- ==> var1) ++> (- ==> var2) ++> (- ==> var))).
Proof.
unfold k2; rauto.
Global Instance k2_unfold RR (R1: klr W A1 B1) (R2: klr W A2 B2) w: Related (RR (R1 w) (R2 w)) (k2 RR R1 R2 w) subrel.
Proof.
red.
reflexivity.
End LIFT.
Global Instance k_rel_params: Params (@k) 4 := { }.
Global Instance k1_rel_params: Params (@k1) 5 := { }.
Global Instance k2_rel_params: Params (@k2) 6 := { }.
Hint Extern 0 (RIntro _ (k _ _) _ _) => eapply k_rintro : typeclass_instances.
Hint Extern 1 (RElim (k _ _) _ _ _ _) => eapply k_relim : typeclass_instances.
Hint Extern 0 (RIntro _ (k1 _ _ _) _ _) => eapply k1_rintro : typeclass_instances.
Hint Extern 1 (RElim (k1 _ _ _) _ _ _ _) => eapply k1_relim : typeclass_instances.
Hint Extern 0 (RIntro _ (k2 _ _ _ _) _ _) => eapply k2_rintro : typeclass_instances.
Hint Extern 1 (RElim (k2 _ _ _ _) _ _ _ _) => eapply k2_relim : typeclass_instances.
Section USUAL.
Context `{kf: KripkeFrame}.
Definition arrow_klr {A1 A2 B1 B2} := k2 (W:=W) (@arrow_rel A1 A2 B1 B2).
Definition arrow_pointwise_klr A {B1 B2} := k1 (W:=W) (@arrow_pointwise_rel A B1 B2).
Definition prod_klr {A1 A2 B1 B2} := k2 (W:=W) (@prod_rel A1 A2 B1 B2).
Definition sum_klr {A1 A2 B1 B2} := k2 (W:=W) (@sum_rel A1 A2 B1 B2).
Definition list_klr {A1 A2} := k1 (W:=W) (@list_rel A1 A2).
Definition set_kle {A B} (R: klr W A B): klr W (A -> Prop) (B -> Prop) := fun w sA sB => forall a, sA a -> exists b, sB b /\ R w a b.
Definition set_kge {A B} (R: klr W A B): klr W (A -> Prop) (B -> Prop) := fun w sA sB => forall b, sB b -> exists a, sA a /\ R w a b.
Definition klr_union {W A B} := k2 (W:=W) (@rel_union A B).
Definition klr_inter {W A B} := k2 (W:=W) (@rel_inter A B).
Definition klr_curry {W A1 B1 C1 A2 B2 C2} := k1 (W:=W) (@rel_curry A1 B1 C1 A2 B2 C2).
End USUAL.
Notation "RA ==> RB" := (arrow_klr RA RB) (at level 55, right associativity) : klr_scope.
Notation "RA ++> RB" := (arrow_klr RA RB) (at level 55, right associativity) : klr_scope.
Notation "RA --> RB" := (arrow_klr (k1 flip RA) RB) (at level 55, right associativity) : klr_scope.
Notation "- ==> R" := (arrow_pointwise_klr _ R) : klr_scope.
Infix "*" := prod_klr : klr_scope.
Infix "+" := sum_klr : klr_scope.
Infix "\/" := klr_union : klr_scope.
Infix "/\" := klr_inter : klr_scope.
Notation "% R" := (klr_curry R) : klr_scope.
Hint Extern 0 (RIntro _ (arrow_klr _ _ _) _ _) => eapply k2_rintro : typeclass_instances.
Hint Extern 1 (RElim (arrow_klr _ _ _) _ _ _ _) => eapply k2_relim : typeclass_instances.
Hint Extern 0 (RIntro _ (arrow_pointwise_klr _ _ _) _ _) => eapply k1_rintro : typeclass_instances.
Hint Extern 1 (RElim (arrow_pointwise_klr _ _ _) _ _ _ _) => eapply k1_relim : typeclass_instances.
Hint Extern 0 (RIntro _ (prod_klr _ _ _) _ _) => eapply k2_rintro : typeclass_instances.
Hint Extern 1 (RElim (prod_klr _ _ _) _ _ _ _) => eapply k2_relim : typeclass_instances.
Hint Extern 0 (RIntro _ (sum_klr _ _ _) _ _) => eapply k2_rintro : typeclass_instances.
Hint Extern 1 (RElim (sum_klr _ _ _) _ _ _ _) => eapply k2_relim : typeclass_instances.
Hint Extern 0 (RIntro _ (list_klr _ _) _ _) => eapply k1_rintro : typeclass_instances.
Hint Extern 1 (RElim (list_klr _ _) _ _ _ _) => eapply k1_relim : typeclass_instances.
Hint Extern 0 (RIntro _ (klr_curry _ _) _ _) => eapply k1_rintro : typeclass_instances.
Hint Extern 1 (RElim (klr_curry _ _) _ _ _ _) => eapply k1_relim : typeclass_instances.
Section MODALITIES.
Context `{kf: KripkeFrame}.
Definition klr_box {A B} (l: L) (R: klr W A B): klr W A B := fun w x y => forall w', acc l w w' -> R w' x y.
Global Instance klr_box_subrel {A B}: Monotonic (@klr_box A B) (- ==> (- ==> subrel) ++> (- ==> subrel)).
Proof.
firstorder.
Definition klr_diam {A B} (l: L) (R: klr W A B): klr W A B := fun w x y => exists w', acc l w w' /\ R w' x y.
Global Instance klr_diam_subrel {A B}: Monotonic (@klr_diam A B) (- ==> (- ==> subrel) ++> (- ==> subrel)).
Proof.
firstorder.
End MODALITIES.
Global Instance klr_box_subrel_params: Params (@klr_box) 4 := { }.
Global Instance klr_diam_subrel_params: Params (@klr_diam) 4 := { }.
Hint Extern 0 (RIntro _ (klr_box _ _ _) _ _) => eapply klr_box_rintro : typeclass_instances.
Hint Extern 1 (RElim (klr_box _ _ _) _ _ _ _) => eapply klr_box_relim : typeclass_instances.
Hint Extern 0 (RExists _ (klr_diam _ _ _) _ _) => eapply klr_diam_rintro : typeclass_instances.
Hint Extern 1 (RElim (klr_diam _ _ _) _ _ _ _) => eapply klr_diam_relim : typeclass_instances.
Notation "[ l ] R" := (klr_box l R) (at level 65) : klr_scope.
Notation "< l > R" := (klr_diam l R) (at level 65) : klr_scope.
Notation "[] R" := (klr_box tt R) (at level 65) : klr_scope.
Notation "<> R" := (klr_diam tt R) (at level 65) : klr_scope.
Section ARROW_MOD.
Context {W L1 L2} `{kf: KripkeFrame (L1 * L2) W}.
Definition klr_boxto {A B} (R : klr W A B) : klr W (L1 -> A) (L2 -> B) := fun w f g => forall l1 l2 w', acc (l1, l2) w w' -> R w' (f l1) (g l2).
Definition klr_diamat {A B} (R : klr W A B) : klr W (L1 * A) (L2 * B) := fun w '(l1, a) '(l2, b) => exists w', acc (l1, l2) w w' /\ R w' a b.
End ARROW_MOD.
Notation "[] -> R" := (klr_boxto R) (at level 65) : klr_scope.
Notation "<> * R" := (klr_diamat R) (at level 65) : klr_scope.
Section UNKRIPKIFY.
Context `{kf: KripkeFrame}.
Definition rel_kvd {A B} (R: klr W A B): rel A B := fun x y => forall w, R w x y.
Global Instance rel_kvd_subrel A B: Monotonic (@rel_kvd A B) ((- ==> subrel) ++> subrel).
Proof.
firstorder.
End UNKRIPKIFY.
Global Instance rel_kvd_subrel_params: Params (@rel_kvd) 3 := { }.
Hint Extern 0 (RIntro _ (rel_kvd _) _ _) => eapply rel_kvd_rintro : typeclass_instances.
Hint Extern 1 (RElim (rel_kvd _) _ _ _ _) => eapply rel_kvd_relim : typeclass_instances.
Notation "|= R" := (rel_kvd R) (at level 65) : rel_scope.
Definition klr_pullw {W1 W2 A B} (f: W1 -> W2) (R: klr W2 A B): klr W1 A B := fun w => R (f w).
Notation "R @@ [ f ]" := (klr_pullw f R) (at level 30, right associativity) : klr_scope.
Global Instance klr_pullw_subrel {W1 W2 A B} RW1 RW2: Monotonic (@klr_pullw W1 W2 A B) ((RW1 ++> RW2) ++> (RW2 ++> subrel) ++> (RW1 ++> subrel)).
Proof.
unfold klr_pullw.
rauto.
Global Instance klr_pullw_subrel_params: Params (@klr_pullw) 5 := { }.
Hint Extern 0 (RIntro _ (klr_pullw _ _ _) _ _) => eapply klr_pullw_rintro : typeclass_instances.
Hint Extern 1 (RElim (klr_pullw _ _ _) _ _ _ _) => eapply klr_pullw_relim : typeclass_instances.

Lemma k1_relim RR (R1: klr W A1 B1) w x y P Q: RElim (RR (R1 w)) x y P Q -> RElim (k1 RR R1 w) x y P Q.
Proof.
tauto.
