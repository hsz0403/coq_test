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

Lemma index_leq (A:finType) (x:A): index x <= length (elem A).
Proof.
eapply Nat.lt_le_incl,index_le.
