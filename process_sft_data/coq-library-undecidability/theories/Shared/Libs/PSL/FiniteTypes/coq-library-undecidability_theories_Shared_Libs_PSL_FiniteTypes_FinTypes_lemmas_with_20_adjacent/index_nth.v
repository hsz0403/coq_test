From Undecidability.Shared.Libs.PSL Require Export BasicDefinitions.
From Undecidability.Shared.Libs.PSL Require Import Bijection.
Class finTypeC (type:eqType) : Type := FinTypeC { enum: list type; enum_ok: forall x: type, count enum x = 1 }.
Structure finType : Type := FinType { type:> eqType; class: finTypeC type }.
Arguments FinType type {class}.
Existing Instance class | 0.
Hint Extern 5 (finTypeC (EqType ?x)) => unfold x : typeclass_instances.
Canonical Structure finType_CS (X : Type) {p : eq_dec X} {class : finTypeC (EqType X)} : finType := FinType (EqType X).
Arguments finType_CS (X) {_ _}.
Definition elem (F: finType) := @enum (type F) (class F).
Hint Unfold elem : core.
Hint Unfold class : core.
Hint Resolve elem_spec : core.
Hint Resolve enum_ok : core.
Hint Resolve allSub : core.
Instance finType_forall_dec (X: finType) (p: X -> Prop): (forall x, dec (p x)) -> dec (forall x, p x).
Proof.
intros D.
eapply dec_transfer.
-
symmetry.
exact (Equivalence_property_all p).
-
auto.
Instance finType_exists_dec (X:finType) (p: X -> Prop) : (forall x, dec (p x)) -> dec (exists x, p x).
Proof.
intros D.
eapply dec_transfer.
-
symmetry.
exact (Equivalence_property_exists p).
-
auto.
Definition finType_cc (X: finType) (p: X -> Prop) (D: forall x, dec (p x)) : (exists x, p x) -> {x | p x}.
Proof.
intro H.
assert(exists x, x el (elem X) /\ p x) as E by firstorder.
pose proof (list_cc D E) as [x G].
now exists x.
Defined.
Definition pickx (X: finType): X + (X -> False).
Proof.
destruct X as [X [enum ok]].
induction enum.
-
right.
intro x.
discriminate (ok x).
-
tauto.
Defined.
Fixpoint getPosition {E: eqType} (A: list E) x := match A with | nil => 0 | cons x' A' => if Dec (x=x') then 0 else 1 + getPosition A' x end.
Definition pos_def (X : eqType) (x : X) A n := match pos x A with None => n | Some n => n end.
Definition index {F: finType} (x:F) := getPosition (elem F) x.

Lemma elem_spec (X: finType) (x:X) : x el (elem X).
Proof.
apply countIn.
pose proof (enum_ok x) as H.
unfold elem.
Admitted.

Lemma allSub (X: finType) (A:list X) : A <<= elem X.
Proof.
intros x _.
Admitted.

Theorem Equivalence_property_all (X: finType) (p: X -> Prop) : (forall x, p x) <-> forall x, x el (elem X) -> p x.
Proof.
Admitted.

Theorem Equivalence_property_exists (X: finType) (p:X -> Prop): (exists x, p x) <-> exists x, x el (elem X) /\ p x.
Proof.
split.
-
intros [x P].
eauto.
-
intros [x [E P]].
Admitted.

Instance finType_forall_dec (X: finType) (p: X -> Prop): (forall x, dec (p x)) -> dec (forall x, p x).
Proof.
intros D.
eapply dec_transfer.
-
symmetry.
exact (Equivalence_property_all p).
-
Admitted.

Instance finType_exists_dec (X:finType) (p: X -> Prop) : (forall x, dec (p x)) -> dec (exists x, p x).
Proof.
intros D.
eapply dec_transfer.
-
symmetry.
exact (Equivalence_property_exists p).
-
Admitted.

Definition finType_cc (X: finType) (p: X -> Prop) (D: forall x, dec (p x)) : (exists x, p x) -> {x | p x}.
Proof.
intro H.
assert(exists x, x el (elem X) /\ p x) as E by firstorder.
pose proof (list_cc D E) as [x G].
Admitted.

Definition pickx (X: finType): X + (X -> False).
Proof.
destruct X as [X [enum ok]].
induction enum.
-
right.
intro x.
discriminate (ok x).
-
Admitted.

Lemma DM_notAll (X: finType) (p: X -> Prop) (D:forall x, dec (p x)): (~ (forall x, p x)) <-> exists x, ~ (p x).
Proof.
Admitted.

Lemma DM_exists (X: finType) (p: X -> Prop) (D: forall x, dec (p x)): (exists x, p x) <-> ~(forall x, ~ p x).
Proof.
split.
-
firstorder.
-
Admitted.

Lemma getPosition_correct {E: eqType} (x:E) A: if Dec (x el A) then forall z, (nth (getPosition A x) A z) = x else getPosition A x = |A |.
Proof.
induction A;cbn.
-
repeat destruct Dec;tauto.
-
Admitted.

Lemma getPosition_nth (X:eqType) k (d :X) xs: Dupfree.dupfree xs -> k < length xs -> getPosition xs (nth k xs d) = k.
Proof.
induction xs in k|-*.
now cbn.
intros H1 H2.
inv H1.
cbn.
destruct k.
-
decide _.
all:easy.
-
decide _.
+
subst a.
cbn in H2.
edestruct H3.
eapply nth_In.
lia.
+
cbn in H2.
rewrite IHxs.
Admitted.

Lemma injective_index (A: finType) (x1 x2 : A) : index x1 = index x2 -> x1 = x2.
Proof.
destruct (elem A) eqn:E.
-
hnf.
intros.
assert (x1 el elem A) by eauto using elem_spec.
rewrite E in H0.
auto.
-
clear E.
eapply (left_inv_inj (g := (fun y => nth y (elem A) e))).
hnf.
intros.
Admitted.

Lemma index_le (A:finType) (x:A): index x < length (elem A).
Proof.
unfold index.
assert (H:x el elem A) by apply elem_spec.
revert H.
generalize (elem A).
intros l H.
induction l;cbn;[|decide _].
-
easy.
-
lia.
-
destruct H.
congruence.
apply IHl in H.
Admitted.

Lemma index_leq (A:finType) (x:A): index x <= length (elem A).
Proof.
Admitted.

Lemma index_nth {F : finType} (x:F) y: nth (index x) (elem F) y = x.
Proof.
unfold index, elem, enum.
destruct F as [[X E] [A all_A]];cbn.
pose proof (getPosition_correct x A) as H.
destruct Dec.
auto.
apply notInZero in n.
now setoid_rewrite all_A in n.
