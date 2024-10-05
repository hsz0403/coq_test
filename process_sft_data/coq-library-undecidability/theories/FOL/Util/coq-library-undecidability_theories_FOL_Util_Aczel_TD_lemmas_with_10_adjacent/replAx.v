From Undecidability.FOL Require Import Util.Aczel.
Require Import Setoid Morphisms.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Class extensional_normaliser := { tdelta : (Acz -> Prop) -> Acz; TDesc1 : forall P, (exists s, forall t, P t <-> Aeq t s) -> P (tdelta P); TDesc2 : forall P P', (forall s, P s <-> P' s) -> tdelta P = tdelta P'; PI : forall s (H H' : tdelta (Aeq s) = s), H = H'; }.
Section QM.
Context { Delta : extensional_normaliser }.
Definition N s := tdelta (Aeq s).
Fact CR1 : forall s, Aeq s (N s).
Proof.
intros s.
pattern (N s).
apply TDesc1.
now exists s.
Global Instance N_proper : Proper (Aeq ==> Aeq) N.
Proof.
intros s t H.
now rewrite <- (CR1 s), <- (CR1 t).
Definition SET := sig (fun s => N s = s).
Definition NS s : SET := exist (fun s => N s = s) (N s) (N_idem s).
Definition IN (X Y : SET) := Ain (proj1_sig X) (proj1_sig Y).
Definition Subq (X Y : SET) := forall Z, IN Z X -> IN Z Y.
Hint Resolve Ain_IN_p1 Ain_IN_NS Ain_IN_p1_NS Ain_IN_NS_p1 IN_Ain_p1 IN_Ain_NS IN_Ain_p1_NS IN_Ain_NS_p1 : core.
Definition Sempty := NS AEmpty.
Definition Supair (X Y : SET) := NS (Aupair (proj1_sig X) (proj1_sig Y)).
Definition Sunion (X : SET) := NS (Aunion (proj1_sig X)).
Definition Spower (X : SET) := NS (Apower (proj1_sig X)).
Definition empred (P : SET -> Prop) := fun s => P (NS s).
Definition Ssep (P : SET -> Prop) (X : SET) := NS (Asep (empred P) (proj1_sig X)).
Definition emfun (F : SET -> SET) := fun s => proj1_sig (F (NS s)).
Definition Srepl (F : SET -> SET) (X : SET) := NS (Arepl (emfun F) (proj1_sig X)).
Definition Som := NS Aom.
Fact empred_Aeq P : cres Aeq (empred P).
Proof.
intros s s' H % Aeq_NS_eq.
unfold empred.
now rewrite H.
Fact emfun_Aeq F : fres Aeq (emfun F).
Proof.
intros s s' H % Aeq_NS_eq.
unfold emfun.
now rewrite H.
Definition desc (P : SET -> Prop) := NS (tdelta (fun s => empred P s)).
Definition Srep (R : SET -> SET -> Prop) X := Srepl (fun x => desc (R x)) (Ssep (fun x => exists y, R x y) X).
Definition functional X (R : X -> X -> Prop) := forall x y y', R x y -> R x y' -> y = y'.
Definition Ssucc X := Sunion (Supair X (Supair X X)).
Definition Sinductive X := IN Sempty X /\ forall Y, IN Y X -> IN (Ssucc Y) X.
End QM.

Lemma Aeq_p1_eq (X Y : SET) : Aeq (proj1_sig X) (proj1_sig Y) -> X = Y.
Proof.
intros H.
rewrite <- (NS_p1_eq Y).
Admitted.

Lemma Aeq_NS_eq s t : Aeq s t -> NS s = NS t.
Proof.
intros H % CR2.
Admitted.

Lemma set_ext X Y : Subq X Y /\ Subq Y X <-> X = Y.
Proof.
split; intros H; try now rewrite H.
destruct H as [H1 H2].
Admitted.

Lemma emptyE X : ~ IN X Sempty.
Proof.
intros H % IN_Ain_p1_NS.
Admitted.

Lemma upairAx X Y Z : IN Z (Supair X Y) <-> Z = X \/ Z = Y.
Proof.
split; intros H.
-
apply IN_Ain_p1_NS, AupairAx in H as [H|H].
+
left.
now apply Aeq_p1_eq.
+
right.
now apply Aeq_p1_eq.
-
apply Ain_IN_p1_NS, AupairAx.
Admitted.

Lemma unionAx X Z : IN Z (Sunion X) <-> exists Y, IN Y X /\ IN Z Y.
Proof.
split; intros H.
-
apply IN_Ain_p1_NS, AunionAx in H as [y[Y1 Y2]].
exists (NS y).
split; auto.
-
destruct H as [Y[Y1 Y2]].
apply Ain_IN_p1_NS, AunionAx.
exists (proj1_sig Y).
Admitted.

Lemma powerAx X Y : IN Y (Spower X) <-> Subq Y X.
Proof.
split; intros H.
-
apply IN_Ain_p1_NS, ApowerAx in H.
now apply ASubq_Subq_p1.
-
apply Ain_IN_p1_NS, ApowerAx.
Admitted.

Fact empred_Aeq P : cres Aeq (empred P).
Proof.
intros s s' H % Aeq_NS_eq.
unfold empred.
Admitted.

Lemma sepAx P X Y : IN Y (Ssep P X) <-> IN Y X /\ P Y.
Proof with try apply empred_Aeq.
split; intros H.
-
apply IN_Ain_p1_NS, AsepAx in H as [H1 H2]...
split; auto.
unfold empred in H2.
now rewrite NS_p1_eq in H2.
-
destruct H as [H1 H2].
apply Ain_IN_p1_NS, AsepAx...
split; trivial.
unfold empred.
Admitted.

Fact emfun_Aeq F : fres Aeq (emfun F).
Proof.
intros s s' H % Aeq_NS_eq.
unfold emfun.
Admitted.

Lemma descAx (P : SET -> Prop) X : P X -> unique P X -> P (desc P).
Proof.
intros H1 H2.
enough (empred P (tdelta (empred P))) by assumption.
apply TDesc1.
exists (proj1_sig X).
intros t.
split; intros H.
-
apply NS_eq_Aeq_p1.
symmetry.
now apply H2.
-
symmetry in H.
apply (empred_Aeq H).
hnf.
Admitted.

Lemma descAx2 (P P' : SET -> Prop) : (forall x, P x <-> P' x) -> desc P = desc P'.
Proof.
intros H.
apply Aeq_NS_eq, Aeq_ref', TDesc2.
intros s.
Admitted.

Lemma repAx R X Y : functional R -> IN Y (Srep R X) <-> exists Z, IN Z X /\ R Z Y.
Proof.
intros H.
unfold Srep.
rewrite replAx.
split; intros [Z[H1 H2]]; exists Z; split.
-
now apply sepAx in H1.
-
apply sepAx in H1 as [_ [Y' H']].
subst.
eapply descAx; firstorder eauto.
-
apply sepAx; split; trivial.
now exists Y.
-
eapply H; eauto.
Admitted.

Lemma Ainductive_Sinductive X : Ainductive (proj1_sig X) <-> Sinductive X.
Proof.
split; intros [H1 H2]; split.
-
now apply Ain_IN_NS_p1.
-
intros Y H % IN_Ain_p1.
apply H2 in H.
unfold IN.
cbn.
now rewrite <- !CR1.
-
now apply IN_Ain_NS_p1.
-
intros s H % Ain_IN_NS_p1.
specialize (H2 (NS s) H).
unfold IN in H2.
cbn in H2.
Admitted.

Lemma omAx1 : Sinductive Som.
Proof.
split.
-
apply Ain_IN_NS.
apply AomAx1.
-
intros X H.
unfold IN in *; cbn in *.
rewrite <- !CR1 in *.
Admitted.

Lemma omAx2 : forall X, Sinductive X -> Subq Som X.
Proof.
intros X H.
apply ASubq_Subq_p1.
cbn.
rewrite <- CR1.
apply AomAx2.
Admitted.

Lemma replAx F X Y : IN Y (Srepl F X) <-> exists Z, IN Z X /\ Y = F Z.
Proof with try apply emfun_Aeq.
split; intros H.
-
apply IN_Ain_p1_NS, AreplAx in H as [z[Z1 Z2]]...
exists (NS z).
split; auto.
now apply Aeq_p1_eq.
-
destruct H as [Z[Z1 Z2]].
apply Ain_IN_p1_NS, AreplAx...
exists (proj1_sig Z).
split; auto.
rewrite Z2.
unfold emfun.
now rewrite NS_p1_eq.
