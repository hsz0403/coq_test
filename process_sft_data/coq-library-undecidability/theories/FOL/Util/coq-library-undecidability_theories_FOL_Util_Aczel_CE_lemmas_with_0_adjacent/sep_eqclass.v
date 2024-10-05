From Undecidability.FOL Require Import Util.Aczel.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Definition CE := forall (P Q : Acz -> Prop), (forall s, P s <-> Q s) -> P = Q.
Section Model.
Definition eqclass P := exists s, P = Aeq s.
Hypothesis ce : CE.
Definition SET' := { P | eqclass P }.
Definition class (X : SET') : Acz -> Prop := proj1_sig X.
Definition ele X Y := forall s t, (class X) s -> (class Y) t -> Ain s t.
Definition sub X Y := forall Z, ele Z X -> ele Z Y.
Hint Resolve Aeq_eqclass : core.
Definition classof (s : Acz) : SET' := exist _ (Aeq s) (Aeq_eqclass s).
Hint Resolve classof_class classof_eq classof_ele classof_sub : core.
Definition empty := classof AEmpty.
Definition upair' X Y u := exists s t, (class X) s /\ (class Y) t /\ Aeq u (Aupair s t).
Definition upair X Y := exist _ (upair' X Y) (upair_eqclass X Y).
Definition union' X t := exists s, (class X) s /\ Aeq t (Aunion s).
Definition union X := exist _ (union' X) (union_eqclass X).
Definition power' X t := exists s, (class X) s /\ Aeq t (Apower s).
Definition power X := exist _ (power' X) (power_eqclass X).
Definition empred (P : SET' -> Prop) := fun s => P (classof s).
Fact empred_Aeq P : cres Aeq (empred P).
Proof.
intros s s' H % classof_eq.
unfold empred.
now rewrite H.
Definition sep' P X t := exists s, (class X) s /\ Aeq t (Asep (empred P) s).
Definition sep P X := exist _ (sep' P X) (sep_eqclass P X).
Definition succ X := union (upair X (upair X X)).
Definition inductive X := ele empty X /\ forall Y, ele Y X -> ele (succ Y) X.
Definition om := classof Aom.
End Model.

Lemma sep_eqclass P X : eqclass (sep' P X).
Proof.
destruct (classof_ex X) as [s ->].
exists (Asep (empred P) s).
apply ce.
intros t.
split; intros H.
-
destruct H as [s'[H1 H2]]; simpl in H1.
now rewrite H2, (Asep_proper (@empred_Aeq P) H1).
-
exists s.
auto.
