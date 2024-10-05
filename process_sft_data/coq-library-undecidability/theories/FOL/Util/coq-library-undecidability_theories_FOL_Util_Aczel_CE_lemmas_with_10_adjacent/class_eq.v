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

Lemma PE (P P' : Prop) : (P <-> P') -> P = P'.
Proof.
intros H.
change ((fun _ : Acz => P) AEmpty = P').
Admitted.

Lemma PI (P : Prop) (H H' : P) : H = H'.
Proof.
assert (P = True) as ->.
apply PE; tauto.
destruct H, H'.
Admitted.

Lemma Aeq_eqclass s : eqclass (Aeq s).
Proof.
Admitted.

Lemma classof_ex X : exists s, X = classof s.
Proof.
destruct X as [P[s ->]]; simpl.
exists s.
Admitted.

Lemma classof_class s : class (classof s) s.
Proof.
simpl.
Admitted.

Lemma classof_eq s t : classof s = classof t <-> Aeq s t.
Proof.
split; intros H.
-
specialize (classof_class s).
intros XX.
rewrite H in XX.
auto.
-
Admitted.

Lemma classof_ele s t : ele (classof s) (classof t) <-> Ain s t.
Proof.
split; intros H.
-
apply H; simpl; auto.
-
intros s' t' H1 H2.
Admitted.

Lemma classof_sub s t : sub (classof s) (classof t) <-> ASubq s t.
Proof.
split; intros H1.
-
intros u H2.
now apply classof_ele, H1, classof_ele.
-
intros Z H2.
destruct (classof_ex Z) as [u ->].
Admitted.

Lemma upair_eqclass X Y : eqclass (upair' X Y).
Proof.
destruct (classof_ex X) as [s ->].
destruct (classof_ex Y) as [t ->].
exists (Aupair s t).
apply ce.
intros z.
split; intros H.
-
destruct H as [s'[t'[H1[H2 H3]]]]; simpl in H1, H2.
now rewrite H1, H2, H3.
-
exists s, t.
simpl.
Admitted.

Lemma union_eqclass X : eqclass (union' X).
Proof.
destruct (classof_ex X) as [s ->].
exists (Aunion s).
apply ce.
intros z.
split; intros H.
-
destruct H as [s'[H1 H2]]; simpl in H1.
now rewrite H1, H2.
-
exists s.
Admitted.

Lemma power_eqclass X : eqclass (power' X).
Proof.
destruct (classof_ex X) as [s ->].
exists (Apower s).
apply ce.
intros t.
split; intros H.
-
destruct H as [s'[H1 H2]]; simpl in H1.
now rewrite H1, H2.
-
exists s.
Admitted.

Fact empred_Aeq P : cres Aeq (empred P).
Proof.
intros s s' H % classof_eq.
unfold empred.
Admitted.

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
Admitted.

Lemma class_eq X X' s s' : Aeq s s' -> class X s -> class X' s' -> X = X'.
Proof.
destruct X as [P HP], X' as [P' HP']; simpl.
intros H1 H2 XX.
assert (H : P = P').
-
destruct HP as [t ->], HP' as [t' ->].
apply ce.
intros u.
rewrite H2, H1, XX.
tauto.
-
subst P'.
now rewrite (PI HP HP').
