Require Export Ensembles.
Require Import EnsemblesImplicit.
Inductive characteristic_function_abstraction {X:Type} (P:X->Prop) (x:X) : Prop := | intro_characteristic_sat: P x -> In (characteristic_function_abstraction P) x.
Definition characteristic_function_to_ensemble {X:Type} (P:X->Prop) : Ensemble X := characteristic_function_abstraction P.
Notation "[ x : X | P ]" := (characteristic_function_to_ensemble (fun x:X => P)) (x ident).

Lemma characteristic_function_to_ensemble_is_identity: forall {X:Type} (P:X->Prop), [ x:X | P x ] = P.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
exact H.
constructor.
exact H.
