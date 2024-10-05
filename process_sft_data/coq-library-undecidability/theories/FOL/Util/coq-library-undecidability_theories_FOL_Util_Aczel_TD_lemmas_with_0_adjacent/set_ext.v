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

Lemma set_ext X Y : Subq X Y /\ Subq Y X <-> X = Y.
Proof.
split; intros H; try now rewrite H.
destruct H as [H1 H2].
apply Aeq_p1_eq, Aeq_ext; now apply ASubq_Subq_p1.
